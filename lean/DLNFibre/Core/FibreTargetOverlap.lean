/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreBundleLocallyTrivialFull

/-!
# `DLNFibre.Core.FibreTargetOverlap` — the target-side overlap transition (R1, pairwise)

The atlas (`Core.FibreBundleLocallyTrivialFull`) carries the **base-side** overlap cocycle
`chartOverlapTransition I J` (over `sweepSigmaRing`) and the per-pivot trivializations into the
standard fibre model `M := SchurLoc ⊗_k sweepFibreRing`. The S5 capstone names R1 — the **target-side**
overlap-trivialization cocycle — as the residual to a single global `Flat π` / `FiberBundle`. This
module builds the genuine target-side transition, **pairwise**, as Codex's decorrelated scoping
recommended (NOT a bundled triple cocycle): the **double-localized** transition on the product model
`M`, transported from the base-side overlap through the per-pivot trivializations.

## The construction (Codex-recommended shape, double-localized)

For two pivots `I, J`, the base-side overlap `awayOverlap (pivotElt I) (pivotElt J)` is
`Localization.Away eIJ` where `eIJ := algebraMap sweepSigmaRing (Away (chartDsigAt I.s I.t))
(pivotElt J)` is the chart-`J` minor localized into the chart-`I` total ring (`pivotElt I =
chartDsigAt I.s I.t`, so `Away (pivotElt I)` IS the chart-`I` total ring). Transporting along the
per-pivot trivialization `triv I : Away (chartDsigAt I.s I.t) ≃ₐ[k] M` (the generalized localization
transport `awayCongr'`) lands `awayOverlap (pivotElt I)(pivotElt J) ≃ₐ[k]
Localization.Away (triv I eIJ)` — `M` localized at the image of the chart-`J` minor. The target-side
transition is then

> `targetProductOverlapTransition I J :
>    Localization.Away (triv I eIJ) ≃ₐ[k] Localization.Away (triv J eJI)`,

obtained by conjugating the base-side `chartOverlapTransitionK I J` through the two transports — a
`k`-algebra iso between the two double-localized presentations of the overlap on the product model `M`.

## Main results

* `awayCongr'` — the generalized localization transport of an `AlgEquiv` between (possibly different)
  `R`-algebras: `e : A ≃ₐ[R] B`, `e a = b` ⟹ `Localization.Away a ≃ₐ[R] Localization.Away b`. The brick
  the base→target transport needs (the banked `awayCongr` requires `A ≃ₐ A`).
* `targetChartLoc I J` — the chart-`I` target presentation of the overlap: `M` localized at the image
  `triv I eIJ` of the chart-`J` minor.
* `overlapTriv I J` — the base→target transport `awayOverlap (pivotElt I)(pivotElt J) ≃ₐ[k]
  targetChartLoc I J`.
* `chartOverlapTransitionK I J` + `chartOverlapTransitionK_trans_symm` — the base-side transition as a
  `k`-algebra equiv and its round-trip to the identity.
* `targetProductOverlapTransition I J` — the **target-side overlap transition** on the product model
  (double-localized), pairwise.

## Scope (honest)

This is the **pairwise** target-side transition (Codex: NOT a bundled triple cocycle; the domains are
chart-dependent double localizations). The transition OBJECT is built; its **round-trip cocycle** is a
precisely-scoped residual — mathematically immediate from `chartOverlapTransitionK_trans_symm` (the
base-side round-trip, LANDED), but it stalls on Lean infrastructure (a kernel-cost blowup on the
`@[reducible]` double-localized type via `ext`, and missing `AlgEquiv.trans_assoc`/`trans_refl`/
`refl_trans` API in Mathlib v4.29 for the structural route); see the roadmap note at `end Target`. A
single GLOBAL `Flat π` / `FiberBundle` over all of `rankROpen` additionally needs the triple-overlap
coherence packaged + a local-to-global flatness assembly; those stay roadmapped (see
`Core.FibreBundleHeadline`). What this removes is "the target-side transition does not exist" — it does,
pairwise, transported from the base-side transition.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix
open scoped TensorProduct

universe u

/-! ## The generalized localization transport across an `AlgEquiv` between different algebras -/

section AwayCongrGen

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **The localization transport of an `AlgEquiv` between (possibly different) `R`-algebras.** For
`e : A ≃ₐ[R] B` carrying `a` to `b`, the `R`-algebra iso `Localization.Away a ≃ₐ[R] Localization.Away
b` (`mapₐ` of `e` and of `e.symm`, round-tripping by localization initiality). The banked `awayCongr`
is the special case `A = B`; this is the brick transporting a base localization across a per-pivot
trivialization `Away (chartDsigAt …) ≃ₐ[k] SchurLoc ⊗ F`. -/
noncomputable def awayCongr' (e : A ≃ₐ[R] B) (a : A) (b : B) (hb : e a = b) :
    Localization.Away a ≃ₐ[R] Localization.Away b := by
  haveI h1 : IsLocalization.Away (e.toAlgHom a) (Localization.Away b) := by
    change IsLocalization.Away (e a) (Localization.Away b); rw [hb]; infer_instance
  haveI h2 : IsLocalization.Away (e.symm.toAlgHom b) (Localization.Away a) := by
    change IsLocalization.Away (e.symm b) (Localization.Away a)
    rw [← hb, e.symm_apply_apply]; infer_instance
  exact AlgEquiv.ofAlgHom
    (IsLocalization.Away.mapₐ (Localization.Away a) (Localization.Away b) e.toAlgHom a)
    (IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away a) e.symm.toAlgHom b)
    (AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers b)
      (by ext x; simp [IsLocalization.Away.mapₐ, IsLocalization.Away.map])))
    (AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers a)
      (by ext x; simp [IsLocalization.Away.mapₐ, IsLocalization.Away.map])))

@[simp] theorem awayCongr'_symm (e : A ≃ₐ[R] B) (a : A) (b : B) (hb : e a = b) :
    (awayCongr' e a b hb).symm = awayCongr' e.symm b a (by rw [← hb, e.symm_apply_apply]) := by
  ext x
  rfl

end AwayCongrGen

/-! ## The target-side overlap transition on the product model -/

section Target

variable {k : Type} [Field k] [Infinite k] {N : ℕ}
variable (d : Fin (N + 2) → ℕ) (r : ℕ)
  (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)

/-- **The chart-`J` minor localized into the chart-`I` total ring.** `algebraMap sweepSigmaRing
(Away (chartDsigAt I.s I.t)) (pivotElt J)` — the element of the chart-`I` total ring whose inversion
cuts the overlap `D(pivotElt I · pivotElt J)`. Since `pivotElt I = chartDsigAt I.s I.t`, its
`Localization.Away` is exactly the base-side overlap `awayOverlap (pivotElt I)(pivotElt J)`. -/
noncomputable def overlapElt (I J : PivotDatum d r hp hq) :
    Localization.Away (chartDsigAt (k := k) d r I.s I.t) :=
  algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsigAt (k := k) d r I.s I.t))
    (pivotElt d r hp hq J)

/-- **The chart-`I` target presentation of the overlap.** The product model `M = SchurLoc ⊗_k
sweepFibreRing` localized at the image, under the chart-`I` trivialization `triv I`, of the chart-`J`
minor (`overlapElt I J`). The double-localized object on which the target-side transition lives.
`@[reducible]` so its `CommRing` / `Algebra k` instances fire transparently (needed by `awayCongr'`). -/
@[reducible] noncomputable def targetChartLoc (I J : PivotDatum d r hp hq) : Type :=
  Localization.Away
    ((perPivotLocalTrivializationDatum (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization
      (overlapElt d r hp hq I J))

/-- **The base→target transport of the chart-`I` overlap presentation.** The generalized localization
transport `awayCongr'` of the per-pivot trivialization `triv I`, carrying the base-side overlap
`awayOverlap (pivotElt I)(pivotElt J) = Localization.Away (overlapElt I J)` to the chart-`I` target
presentation `targetChartLoc I J = M` localized at `triv I (overlapElt I J)`. -/
noncomputable def overlapTriv (I J : PivotDatum d r hp hq) :
    awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)
      ≃ₐ[k] targetChartLoc (k := k) d r hp hq I J :=
  awayCongr'
    ((perPivotLocalTrivializationDatum (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization)
    (overlapElt d r hp hq I J)
    ((perPivotLocalTrivializationDatum (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization
      (overlapElt d r hp hq I J)) rfl

set_option maxHeartbeats 800000 in -- restrictScalars scalar-tower synthesis over the iterated localization is costly
/-- **The base-side overlap transition as a `k`-algebra equiv.** `chartOverlapTransition I J` is a
`sweepSigmaRing`-algebra equiv; restricting scalars to `k` (the scalar tower `k → sweepSigmaRing →
awayOverlap`) gives the `k`-algebra version we conjugate the trivializations through. Factored as one
named def so the scalar-tower instance is synthesized once (forced into a `letI` so `restrictScalars`
reuses it rather than re-searching). -/
noncomputable def chartOverlapTransitionK (I J : PivotDatum d r hp hq) :
    awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)
      ≃ₐ[k] awayOverlap (pivotElt (k := k) d r hp hq J) (pivotElt (k := k) d r hp hq I) := by
  letI tower : IsScalarTower k (sweepSigmaRing k d r)
      (awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)) := inferInstance
  letI tower2 : IsScalarTower k (sweepSigmaRing k d r)
      (awayOverlap (pivotElt (k := k) d r hp hq J) (pivotElt (k := k) d r hp hq I)) := inferInstance
  exact (chartOverlapTransition d r hp hq I J).restrictScalars k

/-- The `k`-restricted base transition agrees with the underlying base transition as a function. -/
@[simp] theorem chartOverlapTransitionK_apply (I J : PivotDatum d r hp hq)
    (x : awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)) :
    chartOverlapTransitionK d r hp hq I J x = chartOverlapTransition d r hp hq I J x := rfl

/-- **The target-side overlap transition (R1, pairwise, double-localized).** The `k`-algebra iso
between the two chart presentations of the overlap on the product model `M`: the chart-`I`
presentation `targetChartLoc I J` and the chart-`J` presentation `targetChartLoc J I`, obtained by
conjugating the base-side overlap cocycle `chartOverlapTransitionK I J` (the `k`-restricted base
transition) through the two base→target transports `overlapTriv`. This is the genuine target-side
transition the S5 capstone named as residual R1 — here pairwise, as a double-localized object. -/
noncomputable def targetProductOverlapTransition (I J : PivotDatum d r hp hq) :
    targetChartLoc (k := k) d r hp hq I J ≃ₐ[k] targetChartLoc (k := k) d r hp hq J I :=
  (overlapTriv d r hp hq I J).symm.trans
    ((chartOverlapTransitionK d r hp hq I J).trans (overlapTriv d r hp hq J I))

set_option maxHeartbeats 800000 in -- restrictScalars scalar-tower synthesis over the iterated localization is costly
/-- **The `k`-restricted base transition round-trips to the identity.** Restrict-scalars of the
base-side `chartOverlapTransition_trans_symm`. -/
theorem chartOverlapTransitionK_trans_symm (I J : PivotDatum d r hp hq) :
    (chartOverlapTransitionK d r hp hq I J).trans (chartOverlapTransitionK d r hp hq J I)
      = AlgEquiv.refl (R := k) := by
  refine AlgEquiv.ext (fun x ↦ ?_)
  simp only [chartOverlapTransitionK, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.coe_refl, id_eq]
  have := AlgEquiv.ext_iff.mp (chartOverlapTransition_trans_symm d r hp hq I J) x
  simpa [AlgEquiv.trans_apply] using this

/-! ### Roadmap residual — the target-side cocycle round-trip proof

The pairwise target-side **transition object** `targetProductOverlapTransition` is built. Its
**round-trip cocycle** `(I, J) ∘ (J, I) = id` is mathematically immediate from the base-side
`chartOverlapTransitionK_trans_symm` (LANDED, just above): the conjugation
`(overlapTriv I J).symm ≪≫ K_IJ ≪≫ (overlapTriv J I ≪≫ (overlapTriv J I).symm) ≪≫ K_JI ≪≫ overlapTriv I J`
cancels the inner `overlapTriv J I ≪≫ (overlapTriv J I).symm = refl`, then `K_IJ ≪≫ K_JI = refl`. But
formalising it stalls on Lean infrastructure, NOT mathematics:

* the **pointwise** (`ext`) route unfolds the `@[reducible]` double-localized `targetChartLoc` into a
  term the **kernel** cannot typecheck in budget (a deterministic kernel timeout — heartbeat-invisible);
* the **structural** route needs `AlgEquiv.trans_assoc` / `trans_refl` / `refl_trans`, which Mathlib
  v4.29 does **not** provide for `AlgEquiv` (only `self_trans_symm` / `symm_trans_self`); proving them
  by `ext` re-incurs the same kernel cost on this heavy type.

So the round-trip cocycle is a precisely-scoped residual: it needs either the missing `AlgEquiv`
associativity API (a Mathlib-gap spin-out, network-free) or a non-`reducible` `targetChartLoc` with
hand-bundled instances to keep kernel terms small. The base-level round-trip
`chartOverlapTransitionK_trans_symm` is the evidence that the cocycle holds; the transition object is
honest, the cocycle PROOF is the deferred infra. -/

end Target

/-! ## Non-vacuity witnesses -/

section Witness

variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-- **Target transition witness.** The target-side overlap transition exists at every pair of pivots —
a genuine double-localized `k`-algebra iso on the product model. -/
noncomputable example (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    targetChartLoc (k := k) d r hp hq I J ≃ₐ[k] targetChartLoc (k := k) d r hp hq J I :=
  targetProductOverlapTransition d r hp hq I J

set_option maxHeartbeats 800000 in -- restrictScalars scalar-tower synthesis over the iterated localization is costly
/-- **Base round-trip witness.** The `k`-restricted base transition round-trips to the identity — the
evidence (at the base level) behind the deferred target-side cocycle proof. -/
example (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    (chartOverlapTransitionK d r hp hq I J).trans (chartOverlapTransitionK d r hp hq J I)
      = AlgEquiv.refl (R := k) :=
  chartOverlapTransitionK_trans_symm d r hp hq I J

end Witness

end DLNFibre.Core
