import DLNFibre.DLN.RLCT.Validate.RouteMChartFactorFold
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# `RouteMConjBlock` — Phase B item 2: the generic det-preserving block conjugation workhorse

The reusable, network-free workhorse for item 2 of the det route (B+b1): conjugate a nonlinear
factor `g : B → B` (with pointwise fderiv `gD`), acting on its OWN space `B`, identity on a "rest"
space `R`, into a full-ambient `ChartFactor` on `A` via any continuous linear equivalence
`E : A ≃L[ℝ] B × R`. The absolute determinant of the conjugated factor's fderiv is the per-point
determinant of `gD` AT the prefix block `(E u).1` — independent of how the rest `R` is structured.
This is precisely the shape the Schur/LDU/chain factors take: each acts on a `Matrix`-shaped block
and is identity elsewhere; `gD` is the banked Phase-A differential
(`schurFrameDeriv`/`lduCoreDeriv`/`chainUnitMap`).

The determinant fact `conjBlock_abs_det` needs ONLY a CLE `E` — the conjugation washes out the
rest and `det_conj` preserves the det, so `|det D| = |det gD|`. The genuine chart-MAP matching
(which `E`, which prefix-read block) is item 3; this file delivers the det/fderiv plumbing
generically.

* `conjBlockMap E g` / `conjBlockDeriv E gD` — the conjugated map / fderiv.
* `conjBlock_hasFDerivAt` — the conjugated map has fderiv `conjBlockDeriv E gD u` at every `u`.
* `conjBlock_abs_det` — `|det (conjBlockDeriv E gD u)| = J ((E u).1)` given `|det (gD b)| = J b`.
* `conjBlockFactor` — the `ChartFactor N` packaging (when `A = Fin N → ℝ`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

section Generic

variable {A B R : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

/-- **The conjugated block map**: `g` acting on the `B`-block of `A` (via `E : A ≃L B × R`),
identity on the rest `R`. -/
noncomputable def conjBlockMap (E : A ≃L[ℝ] B × R) (g : B → B) : A → A :=
  fun u => E.symm (Prod.map g id (E u))

/-- **The conjugated block fderiv** at `u`: `E.symm ∘ (gD (E u).1 ⊕ id) ∘ E` (a CLM on `A`). -/
noncomputable def conjBlockDeriv (E : A ≃L[ℝ] B × R) (gD : B → B →L[ℝ] B) :
    A → (A →L[ℝ] A) :=
  fun u =>
    (E.symm.toContinuousLinearMap.comp
      (((gD (E u).1).prodMap (ContinuousLinearMap.id ℝ R)).comp E.toContinuousLinearMap))

/-- **The conjugated map has the conjugated fderiv at every point** (chain rule: `E.symm`, `E` are
linear CLEs with constant fderiv; the middle map is `Prod.map g id` with fderiv `gD ⊕ id`). -/
theorem conjBlock_hasFDerivAt (E : A ≃L[ℝ] B × R) (g : B → B) (gD : B → B →L[ℝ] B)
    (hg : ∀ b, HasFDerivAt g (gD b) b) (u : A) :
    HasFDerivAt (conjBlockMap E g) (conjBlockDeriv E gD u) u := by
  have hE : HasFDerivAt (E : A → B × R) E.toContinuousLinearMap u := E.hasFDerivAt
  have hmid : HasFDerivAt (Prod.map g id)
      ((gD (E u).1).prodMap (ContinuousLinearMap.id ℝ R)) (E u) :=
    HasFDerivAt.prodMap (p := E u) (hg (E u).1) (hasFDerivAt_id (E u).2)
  have hcomp1 : HasFDerivAt (fun x => Prod.map g id (E x))
      (((gD (E u).1).prodMap (ContinuousLinearMap.id ℝ R)).comp E.toContinuousLinearMap) u :=
    hmid.comp u hE
  have hEsymm : HasFDerivAt (E.symm : B × R → A) E.symm.toContinuousLinearMap
      (Prod.map g id (E u)) := E.symm.hasFDerivAt
  exact hEsymm.comp u hcomp1

/-- **The conjugated factor's abs-det** `= J ((E u).1)` (the per-point det of the block factor `gD`,
read at the prefix block `(E u).1`). The rest `R` washes out (`det (gD ⊕ id) = det gD · 1`) and
`det_conj` preserves the det. -/
theorem conjBlock_abs_det [FiniteDimensional ℝ B] [FiniteDimensional ℝ R]
    (E : A ≃L[ℝ] B × R) (gD : B → B →L[ℝ] B) (J : B → ℝ)
    (hJ : ∀ b, |LinearMap.det (gD b).toLinearMap| = J b) (u : A) :
    |LinearMap.det (conjBlockDeriv E gD u).toLinearMap| = J ((E u).1) := by
  set T : (B × R) →ₗ[ℝ] (B × R) :=
    (gD (E u).1).toLinearMap.prodMap LinearMap.id with hT
  have hconj : LinearMap.det (conjBlockDeriv E gD u).toLinearMap = LinearMap.det T := by
    have heq : (conjBlockDeriv E gD u).toLinearMap
        = (E.symm.toLinearEquiv : (B × R) →ₗ[ℝ] A) ∘ₗ T ∘ₗ
            (E.symm.toLinearEquiv.symm : A →ₗ[ℝ] (B × R)) := by
      rfl
    rw [heq, LinearMap.det_conj T E.symm.toLinearEquiv]
  rw [hconj, hT, LinearMap.det_prodMap, LinearMap.det_id, mul_one, hJ]

end Generic

/-! ## The `ChartFactor N` packaging (`A = Fin N → ℝ`) -/

variable {N : ℕ} {B R : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]

/-- **The conjugated `ChartFactor`**: the generic block conjugation packaged for `composeFold`. -/
noncomputable def conjBlockFactor (E : (Fin N → ℝ) ≃L[ℝ] B × R) (g : B → B) (gD : B → B →L[ℝ] B)
    (hg : ∀ b, HasFDerivAt g (gD b) b) : ChartFactor N where
  f := conjBlockMap E g
  D := conjBlockDeriv E gD
  hasD := conjBlock_hasFDerivAt E g gD hg

omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ R] in
@[simp] theorem conjBlockFactor_f (E : (Fin N → ℝ) ≃L[ℝ] B × R) (g : B → B) (gD : B → B →L[ℝ] B)
    (hg : ∀ b, HasFDerivAt g (gD b) b) :
    (conjBlockFactor E g gD hg).f = conjBlockMap E g := rfl

omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ R] in
@[simp] theorem conjBlockFactor_D (E : (Fin N → ℝ) ≃L[ℝ] B × R) (g : B → B) (gD : B → B →L[ℝ] B)
    (hg : ∀ b, HasFDerivAt g (gD b) b) :
    (conjBlockFactor E g gD hg).D = conjBlockDeriv E gD := rfl

/-- **The conjugated factor's abs-det** (`ChartFactor` form): `= J ((E u).1)`. -/
theorem conjBlockFactor_abs_det (E : (Fin N → ℝ) ≃L[ℝ] B × R) (g : B → B) (gD : B → B →L[ℝ] B)
    (hg : ∀ b, HasFDerivAt g (gD b) b) (J : B → ℝ)
    (hJ : ∀ b, |LinearMap.det (gD b).toLinearMap| = J b) (u : Fin N → ℝ) :
    |LinearMap.det ((conjBlockFactor E g gD hg).D u).toLinearMap| = J ((E u).1) := by
  change |LinearMap.det (conjBlockDeriv E gD u).toLinearMap| = J ((E u).1)
  exact conjBlock_abs_det E gD J hJ u

/-! ## Non-vacuity: a linear block factor conjugated into the ambient telescopes correctly

A LINEAR block factor (a CLM scaling by `3` on a `1`-dim block, identity on the `2`-dim rest)
conjugated into `Fin 3` has constant fderiv with `|det| = 3` everywhere — independent of the split
`E`. Confirms `conjBlockFactor` + `conjBlockFactor_abs_det` fire and the rest washes out. -/
example (E : (Fin 3 → ℝ) ≃L[ℝ] (Fin 1 → ℝ) × (Fin 2 → ℝ)) (u : Fin 3 → ℝ) :
    |LinearMap.det ((conjBlockFactor E
        (fun x => (3 : ℝ) • x)
        (fun _ => (3 : ℝ) • ContinuousLinearMap.id ℝ (Fin 1 → ℝ))
        (fun _ => ((3 : ℝ) • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)).hasFDerivAt)).D u).toLinearMap|
      = |LinearMap.det (((3 : ℝ) • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)).toLinearMap)| :=
  conjBlockFactor_abs_det E _ _ _
    (fun _ => |LinearMap.det (((3 : ℝ) • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)).toLinearMap)|)
    (fun _ => rfl) u

end DLNFibre.DLN.RLCT
