# The citation cordon (+ blueprint-leak guard)

A machine-enforced, forget-proof invariant separating **what is fully formalised** from **what is
cited**, and **what is banked** from **what is still a forecast**. It rides Lean's own kernel
dependency graph — `collectAxioms` for the cited half (the `#print axioms` engine), the
constant-reference graph (`getUsedConstants`) for the blueprint half — so it is complete by
construction: the tag only *accounts*, it can never *conceal*.

Ported from the sibling `qs` (QuillenSuslin) harness and extended here with the `@[blueprint]` guard.
This is the `name = content` / Proved-vs-Cited discipline ([`precision.md`](precision.md),
[`bedrock.md`](bedrock.md)) and the *banked-never-consumes-a-forecast* rule of the expedition map
([`expedition-map.md`](expedition-map.md)) turned into a build check.

## The difference from `qs` — DLNFibre is NOT zero-cite

`qs`'s definition of done is **zero-cite**: its gate runs with `--max-cites 0`, so a green gate means
`UNACCOUNTED=0 CITED=0 LOCATION=0` (**FORMALISED**), and the appearance of *any* cite fails the build.

**DLNFibre's definition of done is different: proved *modulo declared citations*.** The Aoyagi
`rlct = ½·codim` DLN equality (`RlctInterface.cited_aoyagi_dln` — Watanabe's universal `rlct ≤ ½·codim`
bound + Aoyagi's exact DLN computation) is a **legitimate cited interface**, not a hole to be closed by
this expedition. So the gate here certifies:

> no *unaccounted* axiom has crept in, every cite is `@[cited]`-tagged and located, and no *banked*
> declaration rests on a *forecast* — with declared cites **permitted**.

A green DLNFibre gate can therefore read `UNACCOUNTED=0 CITED=1 LOCATION=0 LEAKS=0` and still be green.
The reusable exe is cite-permissive by default (no `--max-cites`); pass `--max-cites N` to impose a
ceiling. `scripts/cordon` does **not** pass `--max-cites 0` (that is a `qs`-specific bar).

## The cited mechanism (the "accounted-axioms" cordon)

For a declaration `D`, Lean's kernel *automatically* tracks every axiom `D` transitively depends on
(`collectAxioms`). The cordon subtracts the two kinds of axiom we *permit*:
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

- **`FOUNDATIONAL`** — the standard-3 allowlist `{propext, Classical.choice, Quot.sound}`. Explicit and
  in one place (`Meta.Cordon.foundationalAxioms`), extensible only for a genuinely foundational axiom —
  never to silence a real cite. The other four axioms of Lean's standard set (`sorryAx`,
  `Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`) are deliberately **not** allowlisted: a
  `sorry` (→ `sorryAx`) or a `native_decide` (→ a generated per-invocation axiom at the v4.29 pin) is
  *meant* to go red.
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
(completeness is the kernel's, not the tag's), so it lands in `UNACCOUNTED`, so the gate goes **red** —
and you are forced to tag+locate it (or prove it). Tagging a wrapper theorem does not help either:
`collectAxioms` reports the underlying axiom names, not theorems that mention them.

## The blueprint mechanism (banked never consumes a forecast)

A declaration tagged **`@[blueprint]`** is a **forecast** — a sketch, placeholder, or map-node stub
that is *not yet banked* (the composition-skeleton discipline of [`expedition-map.md`](expedition-map.md),
where a settled fork lands as a driver + obligation-record, sorried and wired toward the headline). The
rule: a **banked** (non-`@[blueprint]`) result must never transitively rest on a forecast. For a
declaration `D` not itself `@[blueprint]`:

```
BLUEPRINT_LEAKS(D) = { @[blueprint]-tagged constants in D's transitive constant dependencies }
```

`D` is **banked-clean** iff `BLUEPRINT_LEAKS(D) = ∅`. Two properties distinguish this from the cited
half:

- **It walks constants, not axioms.** A forecast can be any `def`/`theorem`/`axiom`, so the leak walk
  follows the full constant-reference graph (`getUsedConstants` over types *and* values, every
  declaration kind — the same edge set as the retro `WalkDecls` instrument), not just the axiom graph.
- **Blueprint-internal consumption is permitted.** A forecast may rest on another forecast (`D` itself
  `@[blueprint]` is excluded from the banked roots). Only a *banked* decl resting on a forecast leaks.

**Forget-proof, same as the cite half.** The tag *accounts* a forecast; the leak walk reads the
kernel's constant graph, so a banked decl that reaches a forecast surfaces whether or not anyone
remembered to think of it as a leak. `--allow-blueprint` declares a scope *blueprint-internal* (the
forecast layer itself): leaks are then reported but not gated.

## What green does — and does not — mean

Green means: **no unaccounted axiom in scope, all cites located, no banked decl rests on a forecast.**
It is *not* a whole trusted-computing-base audit — `unsafe`, `@[implemented_by]`, `@[extern]`, and
plugins live outside the axiom graph (the repo's style discipline bans them separately; this project
uses `decide +kernel`, never `native_decide`). Nor does it vouch for the *honesty* of a source string
or the *consistency* of a cited axiom.

**Green does NOT verify a cite is CONSISTENT or NON-VACUOUS.** The gate accounts an `@[cited]` axiom; it
does not check that the axiom is *true*, *satisfiable*, or *fires at the intended target*. An
inconsistent cited axiom passes green and silently makes everything downstream vacuous; a cite whose
hypotheses can't be met where you use it never fires. So a `@[cited]` axiom needs a **human consistency
+ non-vacuity review**: (1) attempt to derive `False` (hunt for an instance satisfying every hypothesis
where the conclusion fails), and (2) adversarially instantiate the hypotheses at the intended target —
ideally shipping a build-time **instantiability witness** so vacuity fails the build. (In a sibling
harness an RLCT-continuation cite passed the gate green while, as first written, proving `False`; caught
only by counterexample-driven review, not the gate.) A concrete counterexample is the check.

## How to declare a cite

A cite is a declared part of DLNFibre's definition of done, so — like `qs` — **adding one is
operator-gated** (it changes the bar; wait-for-explicit-go, never on silence). Once approved:

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

**Green does NOT verify the hypotheses are SATISFIABLE at the intended target — check both ends.** A
cite can be consistent yet **vacuous**: if its hypotheses can't be met where you intend to use it, it
never fires (and can *masquerade* as consistent — a "fix" may restore consistency only by making the
hypotheses unsatisfiable). This bit the RLCT cite: a worst-point hypothesis `∀ x ∈ supp φ, rlct x₀ ≤
rlct x` quantified over *regular* points where the ℝ-valued `rlct` returns a junk `0` (vs the true
`+∞`), so it silently demanded `rlct x₀ ≤ 0` — unsatisfiable at any genuine singularity, and the only
satisfiable instances were degenerate ones where the *conclusion* was false. Six review rounds all
attacked the conclusion ("can `False` be forced"); none instantiated the hypotheses at the intended
germ. So a cite review has **two** obligations: (1) *attempt to derive `False`* (consistency), and (2)
*adversarially instantiate the hypotheses at the intended target* (non-vacuity). Make (2) a build-time
check: ship an **instantiability witness** — a concrete term discharging every hypothesis at a genuine
target germ (e.g. `K = x²` with a `ContDiffBump`) — so vacuity fails the build, the cordon philosophy
applied to hypotheses rather than axioms. Watch especially for a total ℝ-valued proxy of an `ℝ∪{∞}`
invariant: its junk value inverts inequality hypotheses.

## How to declare a cite

1. Write the cited fact as an `axiom` (not a `theorem` with a `sorry` — a cite is an *assumed external
   result*, and the cordon rejects `@[cited]` on a non-`axiom`). State it at exactly the strength the
   source gives, with its scope guard in the same signature.
2. Tag it `@[cited "<source>"]` — the source string is *structured data* (the manifest is auto-derived
   from it), so make it a precise citation (author, theorem number, section). An empty/whitespace source
   is rejected at elaboration.
3. Put it in a **located cite file**: a module whose last name-component is exactly `Cited` (the generic
   `…/Cited.lean` convention) **or** whose full module name is in `Meta.Cordon.citedFileAllowlist`
   (extend that list, in one place). The module that hosts the axiom must `import Meta.Cordon` so the
   attribute is in scope.
4. Build the *proved* content on top of the axiom. Any downstream theorem that uses it is reported
   `CITED[<source>]` by the cordon, with `UNACCOUNTED = ∅`.

## How to declare a forecast

Tag any declaration `@[blueprint]` (it needs `import Meta.Cordon`). Use it for a composition-skeleton
driver, an obligation-record stub, or any map-node placeholder that is not yet banked. Downstream:
another forecast may consume it freely; a banked result may not — the gate reports the leak, and you
either prove/retire the forecast or (if the consumer is itself still a forecast) tag the consumer
`@[blueprint]`.

## The invariants (what `scripts/cordon` enforces)

The gate runs four independent, deterministic checks over **DLNFibre's own declarations** (scope =
module provenance `DLNFibre`) and **exits nonzero** on any violation (unlike the informational
`scripts/sorries`):

1. **UNACCOUNTED = ∅** — no public declaration rests on an untagged, non-foundational axiom.
2. **LOCATION + TAG** — every `axiom` in scope is `@[cited]` *and* declared in a located cite file.
3. **BLUEPRINT-LEAK = ∅** — no banked decl transitively rests on a `@[blueprint]` forecast (suppress
   with `--allow-blueprint` when auditing the forecast layer itself).
4. **MANIFEST** (`--manifest`) — the per-source cite map + the in-scope forecasts (informational; exit 0).

Scope is by **module provenance** (`sourceModule?`), not decl namespace: a decl/axiom is in scope iff
its source module lies under `DLNFibre/**`. This covers all of DLNFibre without sweeping in Mathlib
(`Mathlib.*` modules), and is robust to any bare-namespace helper authored under `DLNFibre/**`. The
UNACCOUNTED and BLUEPRINT checks are transitively complete for any covered root; the LOCATION check and
the audit roots are module-provenance scoped, so a stray/misplaced axiom in a covered module is caught
even with no covered consumer.
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

### Scope of the checks (honest boundary)

The **UNACCOUNTED** check is transitively complete for any covered root: the kernel tracks every axiom a
covered declaration depends on, through *any* namespace (a cite hidden in `Matrix`/`Ideal`/… is caught the
moment a `DLNFibre`/`RLCT` declaration uses it). But the **LOCATION + TAG** check and the **audit roots** are
scoped by the namespace-prefix allowlist (`Config.nsPrefixes`, default `#[DLNFibre, RLCT]`). Consequences to
be honest about:

- The repo's other **first-party Mathlib-mirror namespaces** — `Matrix`, `Ideal`, `MvPolynomial`, `Aoyagi`,
  … (modules under `DLNFibre/**` whose declarations live in a Mathlib-overlapping bare namespace) — are **not**
  audit roots and are **not** subject to the location check. They are covered only **transitively** (via a
  covered consumer). A `@[cited]` axiom placed directly in one of them, with no covered consumer, would evade
  the quarantine-location invariant; a stray untagged axiom there is caught only if something covered uses it.
  They are excluded because a bare `Matrix`/`Ideal` prefix would also sweep in Mathlib itself.
- Today this is a **latent, unexploited** gap: a full-tree sweep confirms the only cites in the repo are the
  covered three. The gate is correct *as run*; the advertised invariant is just weaker than a naive reading of
  "every axiom is located" suggests.
- **Roadmapped tightening: module-provenance scoping** — key the location/root checks on a declaration's
  *source module* (`DLNFibre/**`) rather than its namespace prefix. That covers the Mathlib-mirror namespaces
  without catching upstream Mathlib, closing the gap regardless of namespace. Adopt it if a cite ever needs to
  live in one of those namespaces.

## The tooling

| tool | what it is | when |
|---|---|---|
| `#audit_cited foo` | in-file command (mirrors `#print axioms`), shows `foo`'s UNACCOUNTED + CITED[sources] | the formaliser's inner loop, right where you prove |
| `#audit_blueprint foo` | in-file command, shows the `@[blueprint]` forecasts `foo` transitively rests on | when wiring a skeleton toward a banked headline |
| `scripts/cordon` | the repo **gate** — builds + runs `lake exe cordon-audit` over `DLNFibre/**` (**nonzero on violation**; cite-permissive) | before commit, alongside `scripts/sorries` |
| `scripts/cordon --manifest` | the per-source cite manifest + in-scope forecasts | generating a status column / a `Cited.lean` header |
| `scripts/cordon-test` | battle-tests the cordon against the adversarial fixtures (`tests/*`) | after any change to the cordon itself |

Output is machine-parseable — a one-line summary `UNACCOUNTED=n CITED=n LOCATION=n LEAKS=n` — plus a
human-readable, deterministically-ordered listing where each violation states its fix. The UNACCOUNTED
and BLUEPRINT checks run a **single batched traversal** over the whole scope (shared `visited` set,
O(reachable constants)); per-decl attribution of a bad axiom / a leaked forecast is a targeted pass
taken only on a red gate.

The mechanism lives in `lean/Meta/{Cordon,CordonAudit}.lean` — a sibling tooling library, OUTSIDE the
DLNFibre math library (which stays tooling-free): `Meta.Cordon` = the `@[cited]` + `@[blueprint]`
attributes + the reusable `auditDecl` core + the blueprint walk + the `#audit_*` commands;
`Meta.CordonAudit` = the env-reading gate logic. The exe root is `lean/scripts/CordonGate.lean`, and the
fixtures are `lean/tests/{CordonFixtures,FixtureCited,CordonClean,CordonLeak}.lean`.

## The adversarial fixtures (the proof the cordon works)

A cordon unproven to catch violations is worthless, so the fixtures — decls with known-expected verdicts
— are the spec, and they live in **separate namespaces** (`CordonFixtures` / `CordonClean` /
`CordonLeak`, not `DLNFibre`) in modules whose names have no `DLNFibre` prefix, so the real gate never
sees their *intentional* violations. `scripts/cordon-test` audits them and asserts the verdicts:

- **`CordonFixtures` + `FixtureCited`** (the violating set) → exit 1, `UNACCOUNTED=5 CITED=2 LOCATION=3
  LEAKS=1`: a fully-proved decl → FORMALISED; a tagged + located cite → CITED[source]; an **untagged**
  axiom → UNACCOUNTED + LOCATION; a `@[cited]` axiom **outside** a located file → LOCATION; a
  **transitive** cite → CITED; an axiom hidden in an **`opaque`**'s value → still UNACCOUNTED (the batch
  traverses `opaqueInfo.value`); a **banked decl resting on a `@[blueprint]` forecast** → BLUEPRINT-LEAK.
- **`CordonClean`** (the green control, DLNFibre's real DoD) → exit 0, `UNACCOUNTED=0 CITED=1 LOCATION=0
  LEAKS=0`: a located cite is **permitted** (green with `CITED=1`), and a blueprint-internal consumer of
  a forecast is not a leak.
- **`CordonLeak`** (the isolated leak) → exit 1 without `--allow-blueprint` (`LEAKS=1`), exit 0 with it.

Plus two elaboration-time rejections: `@[cited]` on a non-`axiom`, and `@[cited ""]` with an empty
source. The load-bearing assertions are the untagged / opaque-hidden / misplaced / blueprint-leak cases
— the proof the gate genuinely catches a forgotten, hidden, misplaced cite or a banked-consumes-a-
forecast leak.

## In-repo kin

[`precision.md`](precision.md) (Proved/Cited) · [`bedrock.md`](bedrock.md) (the taste) ·
[`expedition-map.md`](expedition-map.md) (roots / forecasts / the banked-never-consumes-a-forecast
rule). Disposition: [`../../CLAUDE.md`](../../CLAUDE.md).
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
