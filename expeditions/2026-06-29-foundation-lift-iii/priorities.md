# Priorities — `foundation-lift-iii` (taste ledger)

Controller proposes by VOI; **operator edits this file directly**. Build-the-buildable
([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)). Scoped against
`origin/dev` `5bb7adc2`. Recon CLOSED 2026-06-29 (the 2-phase ladder + the squeeze recalibration).

## Phase 1 — differential-algebra interface  ·  branch `fl3-p1` (off `origin/dev`)

~70% already built + DLN-free. Mostly re-home / consolidate / name-hygiene. Homes:
`Core.RingTheory.Kaehler` + `Core.Dimension.Trdeg`. **Live status → [`threads.md`](threads.md).** As of
the last tick: P1.1 ✅`333a038b`, P1.2 ✅reviewed (leave `[CharZero]` — see below), P1.3/P1.4 ✅verified,
P1.5/P1.6-V2 ✅`1dc6c698`, P1.6-V3 ✅resolved (Mathlib's, no extraction), P1.7+P1.2-finish+P1.6-V1 🔄
(folded "P1-final" rung). **P1.2 crux outcome:** `[CharZero]` is the exact line — `[PerfectField]` is FALSE
(`𝔽_p[T]`, `x=T^p`); char-`p` criterion roadmapped in [`synthesis.md`](synthesis.md), not a chore.

| rung | item | source on dev | target (Mathlib-mirror) | status |
|------|------|---------------|--------------------------|--------|
| P1.1 | generic differential rank (+ `linearIndependent_D_X_fractionRing`, `mapBaseChange_injective_of_formallySmooth`) | `Core/JacobianTrdeg.lean` `genericDifferentialRank` (DLN-free) | `Core/RingTheory/Kaehler/GenericRank.lean` | pending — re-home |
| P1.2 | **`trdeg ≤ generic differential rank` [CRUX]** (`DiffIndepCriterion`/`diffIndepCriterion_proof`/`trdeg_adjoin_le_genericDifferentialRank`) | `Core/JacobianTrdeg.lean` (DLN-free, `[CharZero]` explicit) | Kaehler home + `Core/Dimension/Trdeg.lean` wrapper | pending — **already proved**; **decorrelated review of the char hyp** (`[CharZero]` vs `[PerfectField]`/separable — confirm it composes with the A6.1 perfect-field half) |
| P1.3 | Jacobian orientation + Kähler↔Jacobian bridge | `Core/RingTheory/MvPolynomial/CotangentJacobian.lean` (FL-II P3) | already correct ns | **done** — verify name=content |
| P1.4 | cotangent localization | `Core/RingTheory/Ideal/CotangentLocalization.lean` (FL-II P3) | already correct ns | **done** |
| P1.5 | matrix-Kähler calculus (`derivMatrix_mul_apply`/`derivMatrix_inv_apply`) | `Core/MatrixKaehler.lean` (general `Derivation R A M`) | `Core/RingTheory/Derivation/Matrix.lean` | pending — re-home |
| P1.6 | base-change rank — 3 variants kept **visibly distinct** | V1 `RankMinors.rank_map_eq_of_injective` (done); V2 `MatrixKaehler.finrank_range_baseChange` (done); **V3** (span-dim of a differential family under base change) inlined in `JacobianTrdeg.diffIndepCriterion_proof` | V1→`Matrix.Rank`; V2→`Dimension.Constructions`; **V3→new named lemma beside P1.1** | pending — V1/V2 consolidate-naming; **V3 = extract** |
| P1.7 | image-dim = trdeg (+ consolidate the `AffineNoetherRank` overlap) | `Core/Dimension/{AffineDomain,Localization}.lean` (#14) + `Core/AffineNoetherRank.lean` | `Core/Dimension/AffineDomain` (re-home `trdeg_eq_of_integral_injective`; re-derive `AffineNoetherRank`'s quotient lemma from the f.g.-domain form) | pending — done + consolidate |

**Mathlib:** `Algebra.trdeg` + transcendence-basis API, `KaehlerDifferential` base-change, `FormallySmooth.of_perfectField`, `IsSmoothAt`/smooth-locus all **present-reusable**; the **Jacobian-criterion-for-trdeg ABSENT** (built in-repo, P1.2); image-dim=trdeg packaging **absent** (bespoke, #14).

## Phase 2 — orbit-dimension capstone (the squeeze)  ·  branch `fl3-p2` (off `fl3-p1`) — PROBE-GATED

The squeeze `varietyDim = trdeg ≤ genericDiffRank ≤ finrank(range δ⁰) ≤ cotangent = varietyDim`, de-`Tuple`'d
onto an abstract affine-`G`-variety interface (`R`, `μ*`, `δ⁰`), on Phase 1. ~2400 lines fused.

| rung | item | source | target | status |
|------|------|--------|--------|--------|
| **P2.0** | **DE-`TUPLE` PROBE [GATE]** — write the abstract interface signature (`R`, `μ*`, `δ⁰` + finite-type/smooth instances) + **restate `genericDifferentialRank_…_le_finrank_range_deformationδ` against it without `cochain` types**. Reveals interface-shaped vs irreducibly-`Tuple`-shaped. | `OrbitDifferentialRank` | — | pending — **default proceed on positive; halt+surface only if irreducibly `Tuple`-shaped** |
| P2.1 | trace self-duality brick (`traceFun`/`traceEquiv`, general `{a b : ι → ℕ}`) | `Core/OrbitDifferentialRank.lean` | `Core/.../LinearAlgebra/Matrix/TracePairing` | pending — extract (low risk) |
| P2.2 | **abstract affine-`G`-variety interface** (the de-`Tuple` carrier) | new, modeled on `OrbitVariety`+`OrbitPullbackDim` | `Core/.../AlgebraicGeometry/Group/Orbit` | pending — keystone |
| P2.3 | orbit-as-image irreducibility (`ker μ*` prime) | `Core/OrbitVariety.lean` | P2.2 home | pending — generalize off `BaseChangeGroup` |
| P2.4 | **orbit dim ≤ diff-rank ≤ finrank(range δ⁰) [CRUX]** — the A4.3 adjoint-transpose argument | `Core/OrbitImageDim.lean` + `OrbitDifferentialRank.lean` (672 ln) | P2.2 home, tagging P1.2 | pending — **the big de-`Tuple` refactor** |
| P2.5 | **orbit smooth ⟹ finrank(range δ⁰) = cotangent = orbit dim [CRUX]** — A6.1 | `OrbitTangentCotangent` + `OrbitSmooth` + `OrbitDifferential` (660+552+99 ln), tagging `Dimension/{Smooth,Regular}` | P2.2 home | pending — de-`Tuple` the cotangent-pairing + smoothness |
| P2.6 | squeeze headline `orbit dim = finrank(range δ⁰)` | `Core/VoigtDischarge.lean` | P2.2 home | pending — assemble |

**Stays DLN-local:** `OrbitClosure`/`OrbitKostant`/`Orbit` (type-A box-moves — correct). **Mathlib:** algebraic-group orbit-dimension theory **absent** (this is net-new-to-Mathlib but built-in-repo, fused).

## Crux rungs (decorrelated review)
P1.2 (char hyp — `[CharZero]` vs `[PerfectField]`/separable, composing with A6.1) · P2.4 + P2.5 (the de-`Tuple`
refactor of the Maurer–Cartan/`cochain` machinery; P2.0 probe de-risks first).

## Cross-cutting
- name=content per `/tmp/next-foundational-expedition.md`: object-eq vs `finrank`-eq; the 3 base-change-rank
  variants **named distinctly**; char/separability hyps explicit; no name hiding a cited step.
- Apply L2 (transitive sweep + full-build), L3 (gate next-rung dispatch on completion), L4 (codepoint longLine),
  L5 (re-gate at phase boundaries + crux, not every low-risk re-home). Sibling-clash `rg` per new top-level name.
- Extraction-to-package trigger: not yet (single consumer); namespace-mirror so the eventual move is a file-move.
