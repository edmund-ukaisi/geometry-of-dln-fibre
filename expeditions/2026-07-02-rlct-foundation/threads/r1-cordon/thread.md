# R1 — the citation cordon (thread)

**Kind:** infra (SPECIFY → BUILD → TEST). **Status:** DONE — built, hardened (Codex), battle-tested.
`scripts/cited-test` = **13/13 pass**; the full `DLNFibre` + `AoyagiCited` gate = `UNACCOUNTED=0
CITED=3 LOCATION=0`, OK, ~20 s; `scripts/sorries` = 0 sorry/#exit/native_decide, 3 axiom (the 3
expected cite axioms). All meta modules + fixtures + exe + `AoyagiCited` build clean (no warnings).

## What was built

| file | role |
|---|---|
| `lean/DLNFibre/Core/Meta/Cited.lean` | `@[cited "<source>"]` parametric attribute (`syntax … : attr` + `registerParametricAttribute String`); the reusable `auditDecl` core (`collectAxioms − foundational − @[cited]`); the `#audit_cited foo` command |
| `lean/DLNFibre/Core/Meta/CordonAudit.lean` | env-reading gate logic: `buildReport` (3 checks), `scopedDecls`/`scopedAxioms`, `CordonReport.{ok,summaryLine}`, violation rendering |
| `lean/scripts/CitedAudit.lean` | the `lake exe cited-audit` root — `enableInitializersExecution` + `importModules (loadExts := true)`, arg parsing, nonzero exit |
| `lean/scripts/cited` | the ENFORCING gate wrapper (sibling to `scripts/sorries`) |
| `lean/scripts/cited-test` | the battle-test harness (asserts the fixture verdicts) |
| `lean/tests/{CordonFixtures,FixtureCited}.lean` | adversarial fixtures (the spec), in a SEPARATE namespace so the real gate never sees their intentional violations |
| `lean/DLNFibre/DLN/RLCT/AoyagiCited.lean` | the retrofit: the DLN rlct + 2 bounds as `@[cited]` axioms, the proved `aoyagiRlctRealInterface`, and one cordon-classified payoff — the cordon's first real user |
| `docs/policies/citation-cordon.md` | the policy: mechanism, declare-a-cite workflow, invariants, forget-proofness, what green does/doesn't mean |

## The mechanism (settled)

`UNACCOUNTED(D) = collectAxioms(D) − {propext, Classical.choice, Quot.sound} − @[cited]`. Empty ⟺
proved-modulo-declared-cites. Forget-proof because `collectAxioms` (the kernel) is the completeness
source; the tag only *accounts*. `@[cited]` carries the source as structured data (parametric attr),
so the manifest is auto-derived. Three gate checks: UNACCOUNTED=∅, LOCATION+TAG (every namespace axiom
`@[cited]` + in a located `…Cited` file / allowlist), MANIFEST.

## Fixture verdicts (VERIFIED green)

Auditing the `CordonFixtures` namespace: `UNACCOUNTED=2 CITED=2 LOCATION=2`, **exit 1**.
- (a) `fullyProved` → FORMALISED; (b) `usesCite` → CITED[Fixture Source B]; (e) `transitiveCite` →
  CITED (kernel transitivity).
- (c) `usesUntagged` + the untagged axiom itself → UNACCOUNTED (gate FAILS) — the forget case.
- (d) `misplacedCitedAxiom` (tagged but wrong file) → LOCATION violation (gate FAILS).
- `--manifest` lists `[Fixture Source B] citedFixtureAxiom`, `[Fixture Source D] misplacedCitedAxiom`.
- `#audit_cited` verified: `Nat.add_comm` → FORMALISED; a decl using the located cite → CITED[src].
- `@[cited]` on a non-`axiom` → rejected at elaboration.

The load-bearing (c)/(d) FAIL-when-they-should is the proof the cordon works.

## Decorrelated Codex (xhigh) — findings folded in

Prompt/answer under `codex/`. Codex confirmed soundness + completeness of the predicate and the
forget-proofness argument, and flagged four things, all addressed:
1. **HIGH** — `native_decide` at v4.29 is a *generated per-invocation* axiom, NOT `Lean.ofReduceBool`;
   the cordon still catches it (unaccounted), but the docstring rationale was wrong → **fixed**.
2. **MED** — location rule `endsWith "Cited"` too weak → tightened to *exact* last-component `Cited`
   **or** an explicit `citedFileAllowlist` (which names `…AoyagiCited`, matching the brief).
3. **MED** — the axiom-location scan filtered `isInternalDetail` → now scans **every** namespace axiom
   (so a generated `native_decide` axiom surfaces).
4. **LOW** — permissive string-grab parser → already exact-match `` `(attr| cited $s:str) ``; added
   `@[cited] ⟹ axiom` enforcement.

Codex's precise slogan adopted: **green = "no unaccounted axiom in the imported gate env"**, not a
whole-TCB audit, not source-honesty — documented in the policy + module docstring.

## Retrofit (adapt, not rip-out)

Chose the additive path: `AoyagiCited.lean` declares `rlctReal` + the two bounds as `@[cited]` axioms
and a proved `aoyagiRlctRealInterface : RlctRealInterface` built from them. The generic
`RlctRealInterface` (cite visible in the *type*) stays untouched in `RlctPayoff.lean`; the axioms are
the complementary kernel-tracked form the cordon enforces. Non-breaking — no landed payoff
destabilised — and the corner-`0` payoff specialised to the instance is the cordon's first classified
DLN result (CITED[rlctReal, Watanabe, Aoyagi], UNACCOUNTED = ∅).

## Performance (a real correctness/UX fix)

The first cut ran `collectAxioms` per decl over the whole library — O(decls × depth), timed out at
>590 s. Fixed with `collectAxiomsBatch` (`Cited.lean`): one shared `visited`-set traversal over all
in-scope roots → O(reachable constants). `buildReport`'s UNACCOUNTED check now uses the batched union
(green path = one traversal); per-decl attribution is a targeted pass taken only on a red gate. Full
`DLNFibre` gate dropped from **>590 s (timeout) → ~18–20 s**.

## Controller wiring note (single-writer aggregator)

`AoyagiCited.lean` is NOT imported by `DLNFibre.lean` (I don't edit the single-writer aggregator). Two
things follow: (1) the gate exe's *default* import set includes `DLNFibre.DLN.RLCT.AoyagiCited` so
`scripts/cited` is self-contained; (2) recommend the controller add
`import DLNFibre.DLN.RLCT.AoyagiCited` to `DLNFibre.lean` (append at end) so the aggregator carries the
retrofit and `import DLNFibre` alone is the complete library. Also consider wiring
`DLNFibre.Core.Meta.{Cited,CordonAudit}` into the aggregator so `#audit_cited` is library-wide and the
meta modules are gate-covered by default.
