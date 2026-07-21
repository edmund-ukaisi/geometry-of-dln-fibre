# The citation cordon (+ blueprint-leak guard)

A machine-enforced, forget-proof invariant separating **what is fully formalised** from **what is
cited**, and **what is banked** from **what is still a forecast**. It rides Lean's own kernel
dependency graph — `collectAxioms` for the cited half (the `#print axioms` engine), the
constant-reference graph (`getUsedConstants`) for the blueprint half — so it is complete by
construction: the tag only *accounts*, it can never *conceal*.

This is the `name = content` / Proved-vs-Cited discipline ([`precision.md`](precision.md),
[`bedrock.md`](bedrock.md)) and the *banked-never-consumes-a-forecast* rule of the expedition map
([`expedition-map.md`](expedition-map.md)) turned into a build check.

## The two-part gate (registered roots, no whole-environment walk)

The gate has **two halves**, each riding a native Lean engine — there is no scan of the whole imported
environment (the earlier whole-env `cordon-audit` executable was deleted 2026-07-20; it walked all of
Mathlib and was pathologically slow, and its decl-enumeration was over-strict for expedition mode, where
an imported sorried skeleton is intentional):

1. **The soundness gate — `#assert_banked_clean_batch [<root>, …]`** (a command in `Meta.Cordon`), over
   the roots registered in `lean/DLNFibre/DLN/RLCT/AxCheck.lean`, elaborated when that module is built.
   It runs ONE shared-`visited` `collectAxioms` walk from all roots (the former per-root gate re-walked
   the shared Mathlib subgraph once per root — ~12 min; batched, it is seconds) and asserts the **union**
   of the roots' transitive axioms is **UNACCOUNTED = ∅** and no *banked* root has a **`@[blueprint]`
   leak**. On a clean union it emits a one-line summary that also names the **cited-source SET** in use
   (so a root silently acquiring a permitted cite becomes visible); on a red union it falls back to
   per-root attribution naming the culprit root → axiom/forecast. It does **not** report a per-root
   `CITED[source]` line (that per-root footprint is the batching cost; the four deliverables keep their
   own `#print axioms`), and it does **not** check cite *location* — that is the grep gate's job. The
   per-root `#assert_banked_clean <root>` remains for the inner loop and the fixtures.
   **SCOPE.** This enforces "**no unaccounted axiom UNDER THE REGISTERED ROOTS**", not "every banked
   declaration is clean": a banked result that is never listed is not checked, and the grep half does not
   fail on `sorry`. Completeness therefore relies on the AxCheck root registry being kept current — a new
   load-bearing headline must be added there.
2. **The location + source gate — `scripts/cordon`** (a source-level python grep, sibling to
   `scripts/sorries`). It scans `DLNFibre/**/*.lean` + `DLNFibre.lean` and hard-fails on a cite
   **LOCATION/TAG** violation or any **`native_decide`** token, and prints an informational **blueprint
   census**. It also errors on a **0-files scope** (an empty/nonexistent tree is not a vacuous green).

**Run BOTH — `scripts/cordon-all`.** The two halves are complementary: a green build alone does **not**
establish cite LOCATION; a green `scripts/cordon` alone does **not** establish axiom/forecast
cleanliness. `scripts/cordon-all` runs both in one command (grep, then build `AxCheck` for the soundness
half) so a single "cordon passed" means both held. (`--grep-only` runs just the fast grep half, e.g. in
a pre-commit hook where the full build runs in CI.)

The reusable core (`auditDecl`, the batched walks `collectAxiomsBatch` / `collectBlueprintBatch`, the
slim per-root blueprint walk `blueprintDepsOf`, the attributes, the `#audit_*` reports) lives in
`lean/Meta/Cordon.lean` — a sibling tooling library, OUTSIDE the DLNFibre math library (which stays
tooling-free).

## The difference from `qs` — DLNFibre is NOT zero-cite

`qs`'s definition of done is **zero-cite**: any cite fails its build. **DLNFibre's is *proved modulo
declared citations*.** The Aoyagi `rlct = ½·codim` DLN equality (Watanabe's universal `rlct ≤ ½·codim`
bound + Aoyagi's exact DLN computation) is a **legitimate cited interface**, not a hole this expedition
must close. So a declared, located `@[cited]` axiom is **permitted**: `#assert_banked_clean` on a root
that rests on such an axiom is *green* (the cite is accounted, hence not UNACCOUNTED). Adding a cite
changes the bar, so it is **operator-gated** (wait-for-explicit-go, never on silence).

## The cited mechanism (the "accounted-axioms" cordon)

For a declaration `D`, Lean's kernel *automatically* tracks every axiom `D` transitively depends on
(`collectAxioms`, the engine behind `#print axioms`). The cordon subtracts the two kinds we *permit*:

```
UNACCOUNTED(D) = collectAxioms(D) − FOUNDATIONAL − CITED_TAGGED
```

- **`FOUNDATIONAL`** — the standard-3 allowlist `{propext, Classical.choice, Quot.sound}`, explicit and
  in one place (`Meta.Cordon.foundationalAxioms`), extensible only for a genuinely foundational axiom —
  never to silence a real cite. The other Lean standard axioms (`sorryAx`, `Lean.trustCompiler`,
  `Lean.ofReduceBool`, `Lean.ofReduceNat`) are deliberately **not** allowlisted: a `sorry` (→ `sorryAx`)
  or a `native_decide` (→ a generated per-invocation axiom at the v4.29 pin) is *meant* to go red.
- **`CITED_TAGGED`** — the axioms carrying the `@[cited "<source>"]` attribute.

`D` is **proved modulo declared citations** iff `UNACCOUNTED(D) = ∅`. `#assert_banked_clean D` emits
`D`'s cited footprint and `throwError`s (reddens the build) when `UNACCOUNTED(D) ≠ ∅`.

### Why it is forget-proof

Forgetting the `@[cited]` tag does **not** hide a cite. `collectAxioms` still returns the axiom
(completeness is the kernel's, not the tag's), so it lands in `UNACCOUNTED` and the gate goes **red** —
you are forced to tag+locate it (or prove it). Tagging a wrapper theorem does not help: `collectAxioms`
reports the underlying axiom names, not theorems that mention them. (Verified in `scripts/cordon-test` by
injecting an untagged axiom and confirming the gate reddens.)

## The blueprint mechanism (banked never consumes a forecast)

A declaration tagged **`@[blueprint]`** is a **forecast** — a sketch/placeholder/map-node stub *not yet
banked* (the composition-skeleton discipline of [`expedition-map.md`](expedition-map.md)). The rule: a
**banked** (non-`@[blueprint]`) result must never transitively rest on a forecast. For a declaration `D`
not itself `@[blueprint]`:

```
BLUEPRINT_LEAKS(D) = { @[blueprint]-tagged constants in D's transitive constant dependencies }
```

`D` is **banked-clean** iff `BLUEPRINT_LEAKS(D) = ∅`. Two properties distinguish this from the cite half:

- **It walks constants, not axioms.** A forecast can be any `def`/`theorem`/`axiom`, so the leak walk
  (`blueprintDepsOf`) follows the full constant-reference graph (`getUsedConstants` over types *and*
  values, every declaration kind), not just the axiom graph. The walk **prunes at the first-party
  boundary** (`notUpstream`): an upstream Mathlib/core constant can never reach a first-party forecast,
  so the walk stays `O(first-party graph)`, not `O(reachable Mathlib)`.
- **Blueprint-internal consumption is permitted.** A forecast may rest on another forecast, so
  `#assert_banked_clean` skips GATE 2 when the root is itself `@[blueprint]`. Only a *banked* decl
  resting on a forecast leaks.

## What green does — and does not — mean

Green means: **no unaccounted axiom under the roots, all cites located + tagged, no banked root rests on
a forecast, no `native_decide`.** It is *not* a whole trusted-computing-base audit — `unsafe`,
`@[implemented_by]`, `@[extern]`, and plugins live outside the axiom graph (the style discipline bans
them separately; this project uses `decide +kernel`, never `native_decide`). Nor does it vouch for the
*honesty* of a source string or the *consistency* of a cited axiom.

**Green does NOT verify a cite is CONSISTENT or NON-VACUOUS.** The gate accounts an `@[cited]` axiom; it
does not check that the axiom is *true*, *satisfiable*, or *fires at the intended target*. An
inconsistent cited axiom passes green and silently makes everything downstream vacuous; a cite whose
hypotheses can't be met where you use it never fires (and can masquerade as consistent). So a `@[cited]`
axiom needs a **human consistency + non-vacuity review**: (1) attempt to derive `False` (hunt for an
instance satisfying every hypothesis where the conclusion fails), and (2) adversarially instantiate the
hypotheses at the intended target — ideally shipping a build-time **instantiability witness** so vacuity
fails the build. (In a sibling harness an RLCT-continuation cite passed the gate green while, as first
written, proving `False`; caught only by counterexample-driven review, not the gate.) Watch especially
for a total ℝ-valued proxy of an `ℝ∪{∞}` invariant: its junk value inverts inequality hypotheses.

## How to declare a cite

Adding a cite is **operator-gated** (it changes the definition of done). Once approved:

1. Write the cited fact as an `axiom` (not a `theorem` with a `sorry` — a cite is an *assumed external
   result*; the cordon rejects `@[cited]` on a non-`axiom`). State it at exactly the strength the source
   gives, with its scope guard in the same signature.
2. Tag it `@[cited "<source>"]` — the source string is *structured data* (a precise citation: author,
   theorem number, section). An empty/whitespace source is rejected at elaboration.
3. Put it in a **located cite file**: a module whose last name-component is exactly `Cited` (the generic
   `…/Cited.lean` convention) **or** whose full module name is in `Meta.Cordon.citedFileAllowlist`
   (extend that list, in one place). The grep gate `scripts/cordon` keys the location check on the file
   name (ends in `Cited.lean`, or basename in `{AoyagiCited, FixtureCited}`). The hosting module must
   `import Meta.Cordon` so the attribute is in scope.
4. Build the *proved* content on top of the axiom, and register any headline that rests on it as a root
   in the `#assert_banked_clean_batch [...]` list in `AxCheck.lean` (the batch accounts the cite in its
   union and names its source in the clean summary's cited-source set; `#audit_cited <headline>` gives
   the per-root `CITED[<source>]` footprint).

Example (`DLNFibre/DLN/RLCT/AoyagiCited.lean`):

    @[cited "Watanabe (…): universal bound rlct ≤ ½·codim"]
    axiom cited_watanabe_upper_ax (d : …) (B : …) (r : ℕ) : …

## How to declare a forecast

Tag any declaration `@[blueprint]` (needs `import Meta.Cordon`). Use it for a composition-skeleton
driver, an obligation-record stub, or any map-node placeholder not yet banked. Downstream: another
forecast may consume it freely; a banked result may not — `#assert_banked_clean` on a banked root that
reaches it reddens the build, and you either prove/retire the forecast or tag the consumer `@[blueprint]`.

## The registered roots (`AxCheck.lean`)

`lean/DLNFibre/DLN/RLCT/AxCheck.lean` is `#print`-only (it adds no definitions and no axioms). It
`import Meta.Cordon` + `open Meta.Cordon`, then gates its roots:

- **`#assert_banked_clean_batch [X, Y, …]`** — the single gate line listing every intended-clean root
  (UNACCOUNTED = ∅, no leak) in ONE shared walk. It reddens the build if any listed root regresses (a
  sneaked `sorry`/`native_decide` → `sorryAx`/a generated axiom → UNACCOUNTED; a forecast dependency →
  a leak), and attributes the culprit root. (Duplicate entries are harmless — the walk dedups — but the
  list is kept distinct.)
- **`#print axioms X` + `-- TRACKED-OPEN (live-frontier sorry): informational, NOT gated`** — for a root
  that legitimately carries `sorryAx` today (an open live-frontier rung). These are informational only;
  listing them in the batch would (correctly) redden the build.

The four deliverables — `aoyagi_learning_coefficient_L1`, `_L2`, `_gen`, `_gen_le` — are asserted and
remain clean-three (`[propext, Classical.choice, Quot.sound]`).

## The tooling

| tool | what it is | when |
|---|---|---|
| `#audit_cited foo` | in-file report (mirrors `#print axioms`): `foo`'s UNACCOUNTED + CITED[sources] | the formaliser's inner loop |
| `#audit_blueprint foo` | in-file report: the `@[blueprint]` forecasts `foo` transitively rests on | when wiring a skeleton toward a headline |
| `#assert_banked_clean_batch [foo, …]` | the **soundness gate** over ALL registered roots in ONE shared walk (asserts the union has UNACCOUNTED = ∅ + no leak; clean-summary names the cited-source set); reddens the build on violation | the gate line in `AxCheck.lean` |
| `#assert_banked_clean foo` | the per-root soundness gate (same assertion, one root) | the inner loop / fixtures |
| `scripts/cordon` | the **grep gate** — cite LOCATION/TAG + `native_decide` ban + blueprint census (**nonzero on violation**; errors on a 0-files scope) | before commit, alongside `scripts/sorries` |
| `scripts/cordon-all` | runs **BOTH halves** (grep + build `AxCheck`) so one "cordon passed" means both; `--grep-only` for the fast half | the single combined check |
| `scripts/cordon-test` | battle-tests both gate halves against the adversarial fixtures | after any change to the cordon itself |

`scripts/cordon` takes an optional `TREE` argument (a directory to scan instead of the DLNFibre tree) —
`scripts/cordon-test` points it at a fixture tree. `scripts/sorries` stays the raw informational census.

## The adversarial fixtures (the proof the cordon works)

A cordon unproven to catch violations is worthless, so the fixtures — decls with known-expected verdicts
in **separate namespaces** (`CordonFixtures` / `CordonClean` / `CordonLeak`, not `DLNFibre`; modules with
no `DLNFibre` prefix, so the real gate never sees them) — are the spec. `scripts/cordon-test` exercises
both halves:

- **soundness half** (scratch modules, checked by `lake env lean` exit code + message):
  a clean cited decl → **succeeds** (a declared cite is permitted); an **untagged**-axiom consumer →
  fails naming the UNACCOUNTED axiom; an axiom hidden in an **`opaque`**'s value → still fails (Lean's
  `collectAxioms` traverses `opaqueInfo.value`); a **banked** decl resting on a `@[blueprint]` forecast →
  fails naming the leaked forecast. Both per-root `#assert_banked_clean` AND batched
  `#assert_banked_clean_batch` are exercised, including the opaque-hidden axiom through the batch
  **fast path** (guards `collectAxiomsBatch`'s opaque arm) and an **empty root list** (errors — no
  vacuous green). Plus two elaboration rejections: `@[cited]` on a non-`axiom`, and `@[cited ""]`
  (empty source).
- **`scripts/cordon` half** (fixture tree): fails naming an untagged axiom, a misplaced cite, and a
  `native_decide`; passes a tree whose only axiom is located + tagged; ERRORS on a 0-files scope. Plus
  the source-scanner **false-negative regressions** (external review, 2026-07-20): a **unicode**-named
  axiom is detected; a same-line `@[cited]` **consumed** by its own declaration does not tag the next
  axiom; a `/-` inside a **string literal** does not comment out later axioms.

`scripts/cordon-test` exits 0 iff every assertion holds, and reddens if the mechanism is broken (verified
by temporarily disabling GATE 1 — the untagged/opaque cases then fail to fail, and the test goes red; and
each false-negative regression scans green under the pre-fix scanner, so its check red-fails without the fix).

## In-repo kin

[`precision.md`](precision.md) (Proved/Cited) · [`bedrock.md`](bedrock.md) (the taste) ·
[`expedition-map.md`](expedition-map.md) (roots / forecasts / the banked-never-consumes-a-forecast
rule). Disposition: [`../../CLAUDE.md`](../../CLAUDE.md).
