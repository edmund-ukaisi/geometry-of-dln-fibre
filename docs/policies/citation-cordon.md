# The citation cordon

A machine-enforced, forget-proof invariant separating **what is fully formalised** from **what is
cited**. Cited external results (the *monuments* — resolution of singularities, Aoyagi's RLCT
computation, Watanabe's universal bound) are Lean `axiom`s, tagged with their source and quarantined
to located `…Cited.lean` files; a filtered report over Lean's own `collectAxioms` (the `#print axioms`
engine) is the gate. This is the `name = content` / Proved-vs-Cited discipline
([`precision.md`](precision.md), [`bedrock.md`](bedrock.md)) turned into a build check.

## The mechanism (the "accounted-axioms" cordon)

For a declaration `D`, Lean's kernel *automatically* tracks every axiom `D` transitively depends on
(`collectAxioms`, the engine behind `#print axioms`). The cordon subtracts the two kinds of axiom we
*permit*:

```
UNACCOUNTED(D) = collectAxioms(D) − FOUNDATIONAL − CITED_TAGGED
```

- **`FOUNDATIONAL`** — the standard-3 allowlist `{propext, Classical.choice, Quot.sound}`. Explicit
  and in one place (`DLNFibre.Meta.Cited.foundationalAxioms`), extensible only for a genuinely
  foundational axiom — never to silence a real cite. The other four axioms of Lean's standard set
  (`sorryAx`, `Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`) are deliberately **not**
  allowlisted: a `sorry` (→ `sorryAx`) or a `native_decide` (→ a generated per-invocation axiom at the
  v4.29 pin) is *meant* to go red.
- **`CITED_TAGGED`** — the axioms carrying the `@[cited "<source>"]` attribute.

`D` is **proved modulo declared citations** iff `UNACCOUNTED(D) = ∅`.

### Why it is forget-proof

Forgetting the `@[cited]` tag does **not** hide a cite. `collectAxioms` still returns the axiom
(completeness is the kernel's, not the tag's), so the axiom lands in `UNACCOUNTED`, so the gate goes
**red** — and you are forced to tag+locate it (or prove it). The tag only *accounts* for an axiom that
is already tracked; it can never *conceal* one. Tagging a wrapper theorem does not help either:
`collectAxioms` reports the underlying axiom names, not theorems that mention them.

### What green does — and does not — mean

Green means: **no unaccounted axiom in the imported gate environment.** It is *not* a whole trusted-
computing-base audit — `unsafe`, `@[implemented_by]`, `@[extern]`, and plugins live outside the axiom
graph (the repo's style discipline bans them separately, and this project uses `decide +kernel`, never
`native_decide`). Nor does it vouch for the *honesty* of a source string: the machine enforces
**accounting** (every cite is a tracked, located axiom); a **human reviews** that the source string is
the right theorem. Keep the caveat next to the claim, as always.

**Green does NOT verify a cite is CONSISTENT.** The gate accounts an `@[cited]` axiom; it does not
check that the axiom is *true* — or even *satisfiable*. An inconsistent cited axiom (one whose body is
false at some instance satisfying its hypotheses) passes green and silently makes everything downstream
vacuous. This is not hypothetical: the RLCT continuation cite passed the gate green while, as first
written, proving `False` (an `∃`-body demanding a pole where the pinned continuation was holomorphic;
caught only by counterexample-driven review, not the gate). So a `@[cited]` axiom needs a **consistency
review** — not just source-faithfulness: hunt for an instance satisfying every hypothesis where the
conclusion fails. An axiom that *pins a unique object* (e.g. `∀ …, Z = f` via an identity theorem) is
especially prone — a later conjunct can contradict the pinned object. Consistency is a human/reviewer
job; a concrete counterexample is the check.

## How to declare a cite

1. Write the cited fact as an `axiom` (not a `theorem` with a `sorry` — a cite is an *assumed external
   result*, and the cordon rejects `@[cited]` on a non-`axiom`). State it at exactly the strength the
   source gives, with its scope guard in the same signature.
2. Tag it `@[cited "<source>"]` — the source string is *structured data* (the manifest is auto-derived
   from it), so make it a precise citation (author, theorem number, paper section). An empty/whitespace
   source is rejected at elaboration (the accounting only means something if a human can review it).
3. Put it in a **located cite file**: a module whose last name-component is exactly `Cited` (the generic
   `…/Cited.lean` convention) **or** whose full module name is in
   `DLNFibre.Meta.Cited.citedFileAllowlist` (extend that list, in one place, for a named cite file such
   as `…/AoyagiCited.lean`).
4. Build the *proved* content on top of the axiom. Any downstream theorem that uses it will be reported
   `CITED[<source>]` by the cordon, with `UNACCOUNTED = ∅`.

Example (the DLN payoff's first real user — `DLNFibre/DLN/RLCT/AoyagiCited.lean`):

    @[cited "Watanabe: universal RLCT upper bound rlct ≤ ½·codim"]
    axiom cited_watanabe_upper_ax (d : …) (B : …) (r : ℕ) :
      0 < N → B.rank = r → (∀ k', r ≤ d k') →
      rlctReal d (lossDLN d B) ≤ ((codimRealFibre d B).toNat : ℝ) / 2

## The invariants (what `scripts/cited` enforces)

The gate runs three independent, deterministic checks over the **first-party namespaces** (default
`#[DLNFibre, RLCT]`) and **exits nonzero** on any violation (unlike the informational `scripts/sorries`).
*First-party bare namespaces* (a module under `DLNFibre/**` whose declarations live in a bare
Mathlib-mirror namespace, e.g. `RLCT`) must be listed in the allowlist (`Config.nsPrefixes` /
`--ns`) to be covered — a namespace-prefix scan of `DLNFibre` alone would miss them, which is exactly
where a cite could otherwise land unmonitored:

1. **UNACCOUNTED = ∅** — no public declaration rests on an untagged, non-foundational axiom.
2. **LOCATION + TAG** — every `axiom` under the namespace is `@[cited]` *and* declared in a located
   cite file (rule above). A stray/untagged axiom anywhere, or a `@[cited]` axiom in the wrong file,
   fails.
3. **MANIFEST** (`--manifest`) — the per-source cite map, derived from the same `@[cited]` sources
   (informational; exit 0).

## The tooling

| tool | what it is | when |
|---|---|---|
| `#audit_cited foo` | in-file command (mirrors `#print axioms`), shows `foo`'s UNACCOUNTED + CITED[sources] | the formaliser's inner loop, right where you prove |
| `scripts/cited` | the repo **gate** — builds + runs `lake exe cited-audit` over the first-party namespaces (`DLNFibre` + `RLCT`), **nonzero on violation** | before commit / in CI, alongside `scripts/sorries` |
| `scripts/cited --manifest` | the per-source cite manifest | generating the README 🔵 status column / a `Cited.lean` header |
| `scripts/cited-test` | battle-tests the cordon against the adversarial fixtures (`tests/CordonFixtures.lean`) | after any change to the cordon itself |

Output is machine-parseable — a one-line summary `UNACCOUNTED=n CITED=n LOCATION=n` — plus a
human-readable, deterministically-ordered listing where each violation states its fix verbatim. The
UNACCOUNTED check runs a **single batched axiom traversal** over the whole namespace (shared `visited`
set, O(reachable constants), not O(decls × depth)), so the full `DLNFibre` gate is ~20 s; per-decl
attribution of a bad axiom is a targeted pass taken only on a red gate.

The mechanism lives in `lean/DLNFibre/Core/Meta/{Cited,CordonAudit}.lean` (the attribute + the reusable
`auditDecl` core + the `#audit_cited` command; the env-reading gate logic), the exe root in
`lean/scripts/CitedAudit.lean`, and the fixtures in `lean/tests/{CordonFixtures,FixtureCited}.lean`.

## The adversarial fixtures (the proof the cordon works)

A cordon unproven to catch violations is worthless, so the fixtures — decls with known-expected
verdicts — are the spec, and they live in a **separate namespace** (`CordonFixtures`, not `DLNFibre`)
so their *intentional* violations never touch the real gate. `scripts/cited-test` audits them and
asserts the verdicts:

- **(a)** a fully-proved decl → **FORMALISED** (`UNACCOUNTED = ∅`, `CITED = ∅`);
- **(b)** a decl using a tagged + located cite → **CITED[source]**;
- **(c)** a decl using an **untagged** axiom → **UNACCOUNTED**, gate **fails**;
- **(d)** a `@[cited]` axiom **outside** a located cite file → **LOCATION** violation, gate **fails**;
- **(e)** a **transitive** cite (`A` uses `B`, `B` cited) → **CITED** (kernel transitivity);
- **(f)** an axiom hidden in an **`opaque`**'s value → still **UNACCOUNTED** (the batch traverses
  `opaqueInfo.value`) — the regression guard for the custom `collectAxiomsBatch`'s completeness.

Plus two elaboration-time rejections (`scripts/cited-test` builds a scratch file and asserts it fails
to compile): `@[cited]` on a non-`axiom`, and `@[cited ""]` with an empty/whitespace source (a cite
must carry a reviewable source).

The load-bearing assertions are (c), (d), (f): the fixture namespace audits to
`UNACCOUNTED=5 CITED=2 LOCATION=3` with exit 1, naming the untagged / opaque-hidden / misplaced axioms
— the proof the gate genuinely catches a forgotten, hidden, or misplaced cite.
