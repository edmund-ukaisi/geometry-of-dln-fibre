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

```
UNACCOUNTED(D) = collectAxioms(D) − FOUNDATIONAL − CITED_TAGGED
```

- **`FOUNDATIONAL`** — the standard-3 allowlist `{propext, Classical.choice, Quot.sound}`. Explicit and
  in one place (`Meta.Cordon.foundationalAxioms`), extensible only for a genuinely foundational axiom —
  never to silence a real cite. The other four axioms of Lean's standard set (`sorryAx`,
  `Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`) are deliberately **not** allowlisted: a
  `sorry` (→ `sorryAx`) or a `native_decide` (→ a generated per-invocation axiom at the v4.29 pin) is
  *meant* to go red.
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
