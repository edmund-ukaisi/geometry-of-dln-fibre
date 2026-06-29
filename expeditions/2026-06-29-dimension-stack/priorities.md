# Priorities — `dimension-stack` (taste ledger)

Controller proposes by VOI; **operator edits this file directly**. Foundation-first, build-the-buildable
([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)).

## The recon (opening wave) — CLOSED 2026-06-28

The AG-foundations scout produced the library ladder. **Headline = the affine dimension stack (entry 1)** —
field-general, `Tuple`-free, Mathlib-absent (grep-verified), and among the most-requested missing Mathlib
commutative-algebra facts (upstream-worthy). **Entry 2 (smooth ⟹ regular)** sits directly on it. Entries 3–5
(orbit-geometry capstone, type-A Gabriel/`Ext`, q-series) stay **DLN-local** — fused to `Tuple`/box-moves;
calling them "general" today would overclaim. Build-vs-cite line: entries 1–2 buildable detail; the analytic
`rlct = ½·codim` is the monument (Cited).

## The ladder (rungs)

| rung | item | source module(s) | target namespace | status |
|------|------|------------------|------------------|--------|
| **R0** | **gate** — throwaway generalisation pass on `NullstellensatzCodim` (strip `RepCoord d`, `σ : Type*`, general `k`, comment out the `[IsAlgClosed]` geometric reading) → confirm the field-general core's *exact* minimal hyps; **revert** (finding is the deliverable). + Mathlib master/PR in-flight check for `IsCatenary` / the catenary equality. | `NullstellensatzCodim` | — | **closed — CONFIRMED (2026-06-29); see R0 outcome below** |
| R1 | integral-extension dimension invariance (`ringKrullDim_eq_of_integral_injective` + going-up chain-lift) | `IntegralDimension` | `Core.Dimension.Integral` (+ `Dimension.Basic`) | **done** (`f447c0ce`; reviewed PASS; re-gate PASS 3819 green) |
| R2 | polynomial-ring catenary (L5) + monic positioning — handle the `private` Mathlib Noether-normalization substitution **in-repo** (re-derive / use the public `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`); do **not** block on an upstream de-privatise PR | `NoetherMonicPositioning`, `PolynomialDimension` | `Core.Dimension.Catenary` | **DONE + SIGNED OFF** (`574a9056`; private-substitution re-derived in-repo, Codex-confirmed; re-gate PASS 3819 green; crux-review **PASS** — verbatim copy byte-faithful, any-field generality sound; 2 cosmetic fixes folded into R3) |
| R3 | finite-type-domain catenary (L4d) + closed-point corollaries (`height_eq_ringKrullDim_of_isMaximal`, local↔global) | `AffineDomainDimension` | `Core.Dimension.AffineDomain` (new file — distinct Mathlib home) | **DONE + PASS** (`f3670561`; headline `affine_domain_height_add_ringKrullDim_quotient_eq` any-field + closed-point corollaries + integral-height-transport brick; peer crux-audit **PASS-with-notes**; 2 wording cosmetics [00OS "exactly"→"restatement"; 5 longLines] + aggregator re-gate folded into R4) |
| R4 | codim bridge (L0): `varietyDim`, `height(vanishingIdeal Z) + varietyDim Z = card` — **split** the field-general catenary/codim core from the `[IsAlgClosed]` geometric `varietyDim` reading | `NullstellensatzCodim` | `Core.Dimension.Codimension` | **DONE + PASS** (`2a610f8f`; field-general core extracted at `[Field k][Finite σ]`, no closure; `vanishingIdeal_isRadical` docstring fixed; `vanishingIdeal_univ_eq_bot` weakened `[IsAlgClosed]→[Infinite k]`; reviewer PASS 6/6 + Codex CLEAN; controller re-gate PASS 3820) |
| E1 | étale local-dimension bridge + `Ideal.height_eq_under_of_etale` | `FlatQuasiFiniteHeight`, `SmoothLocalRelativeDimension` | `Core.Dimension.Smooth` | pending |
| E2 | smooth point ⟹ regular local ring, with the **`[IsAlgClosed] → [PerfectField]`** generalisation | `SmoothPointRegular` | `Core.Dimension.Smooth` | pending |
| RF | retrofit DLN consumers (`codimRep`/`codimRepCanonical`/orbit-dim/fibre-codim) to tag to the general core; delete bespoke; green-gate | (consumers) | — | pending |

## R0 outcome — CONFIRMED, boundary pinned (2026-06-29)

The de-risk probe confirmed (stronger than the recon): `NullstellensatzCodim`'s catenary/codimension **core**
is field-general — exact minimal hyps **`[Field k] [Finite σ]`** (the index `σ` is already `Type*`;
`[CharZero]` is absent; trial build green + axiom-clean `[propext, Classical.choice, Quot.sound]`). Clean
**3-band split** (a clean cut, not a tangle — the geometric band feeds no core theorem):

- **field-general core** → extract to `Core.Dimension.Codimension` (R4): `IsZariskiClosed`/`IsZariskiIrreducible`,
  `isZariskiIrreducible_iff_isPrime_vanishingIdeal`, `vanishingIdeal_isRadical` (already general —
  no-nilpotents, not Nullstellensatz), `ringKrullDim_mvPolynomial_finite`,
  `height_add_ringKrullDim_quotient_eq_card`, `varietyDim`, `height_vanishingIdeal_add_varietyDim_eq_card`,
  `height_vanishingIdeal_eq_card_sub_varietyDim`.
- **`[IsAlgClosed]` geometric/non-vacuity layer** (stays): `nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal`,
  `vanishingIdeal_univ_eq_bot` (true need is `[Infinite k]`), the non-vacuity `example`.
- **DLN consumers** → retrofit (RF): `codimRep_*` — their `[IsAlgClosed]` is **dead weight** (proved removable
  via `_NOALG` variants); RF drops it. A free generalisation win.

Plan corrections from R0:
- The **`[IsAlgClosed] → [PerfectField]` win is E2-only** (smooth/étale stack), NOT the codim bridge: the
  geometric layer's `[IsAlgClosed]` routes through Mathlib's `vanishingIdeal_zeroLocus_eq_radical` (no
  `PerfectField` path). R4 unaffected (its core never touches it).
- **name=content fix for R4:** `vanishingIdeal_isRadical`'s docstring is stale ("over an algebraically closed
  field / strong Nullstellensatz") — the proof is field-general; fix on extract.
- Source already general: the underlying L5 catenary `height_add_ringKrullDim_quotient_eq`
  (`Core.NoetherMonicPositioning`) is `(k : Type*) [Field k]` — R2/R3 inherit.

**Gate PASSED → the ladder commits.**

## ENTRY-1 COMPLETE (2026-06-29) — the affine dimension stack stands

R1–R4 done + reviewed + controller-re-gated green (3820, axiom-clean). The Mathlib-grade, **any-field**,
`Tuple`-free affine dimension library now lives in `DLNFibre.Core.Dimension.*` (5 modules: `Integral`,
`Basic`, `Catenary`, `AffineDomain`, `Codimension`) — the upstream-worthy headline (integral-extension dim
invariance + catenary equality + finite-type-domain dimension formula + the height↔dim codimension bridge),
all Mathlib-absent at `v4.29`. Remaining: **entry-2** (E1 étale local-dim bridge → E2 smooth ⟹ regular,
with the `[IsAlgClosed]→[PerfectField]` win) and **RF** (retrofit DLN consumers — drop the dead-weight
`[IsAlgClosed]`; fix the `DeepChartRing.lean:138` stale prose flagged by R4; the `DLNFibre.lean:430` longLine).

## Highest-suspicion (decorrelated-review the crux)

R2 monic-positioning (the `private`-Mathlib interaction); R4 the field-general / `[IsAlgClosed]` split-point;
E2 the `[IsAlgClosed] → [PerfectField]` weakening (confirm no later lemma silently re-needs algebraic
closure — the scout flagged both R4 and E2 as asserted-from-docstring, not trial-built).

## Roadmap (future expeditions — NOT this one)

orbit-geometry capstone de-`Tuple`-coupling (recon entry 3); type-A Gabriel/`Ext` (4); q-series (5); the
actual mathlib4 upstream PR process; package extraction to a shared library (surface as a **knowing
decision** when a cross-repo dependency is wired).
