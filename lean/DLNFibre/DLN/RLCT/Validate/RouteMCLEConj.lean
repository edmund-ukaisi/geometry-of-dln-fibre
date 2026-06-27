import DLNFibre.DLN.RLCT.Validate.RouteMChartFactorFold
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# `RouteMCLEConj` — whole-space CLE conjugation of a factor into the flat ambient

The OPTION-1 bridge design (`thread.md` UPDATE-8, `codex/bridge-design-*`) builds the achiever-chart
factors as `paramsEquivFlat ∘ Op ∘ paramsEquivFlat.symm` for layer-ops `Op : Params M → Params M`,
so that `composeFold fs = paramsEquivFlat ∘ (composeFold Ops) ∘ paramsEquivFlat.symm` and the bridge
`composeFold fs = phiFlatStructV` becomes a `Params`-LEVEL equality (a clean `funext s`), not an
opaque-width flat induction.

This module is the reusable workhorse for that: conjugate a self-map `g : W → W` of ANY space `W`
(here `W = Params M`) into a full-ambient `ChartFactor N` via a WHOLE-space CLE
`E : (Fin N → ℝ) ≃L[ℝ] W` (no block split — the whole flat space is `W`). The absolute determinant of
the conjugated factor's fderiv is exactly `|det (gD (E u))|` (the conjugation by a CLE is det-preserving,
`det_conj`). This is the `B`-only specialization of `RouteMConjBlock` with a trivial rest.

* `cleConjMap E g` / `cleConjDeriv E gD` — the conjugated map / fderiv.
* `cleConj_hasFDerivAt` — `cleConjMap` has fderiv `cleConjDeriv E gD u` at every `u`.
* `cleConj_abs_det` — `|det (cleConjDeriv E gD u)| = |det (gD (E u))|`.
* `cleConjFactor` — the `ChartFactor N` packaging.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

section Generic

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ}

/-- **The whole-space CLE-conjugated map** `E.symm ∘ g ∘ E`. -/
noncomputable def cleConjMap (E : (Fin N → ℝ) ≃L[ℝ] W) (g : W → W) : (Fin N → ℝ) → (Fin N → ℝ) :=
  fun u => E.symm (g (E u))

/-- **The conjugated fderiv at `u`**: `E.symm ∘ gD (E u) ∘ E` (a CLM on `Fin N → ℝ`). -/
noncomputable def cleConjDeriv (E : (Fin N → ℝ) ≃L[ℝ] W) (gD : W → W →L[ℝ] W) :
    (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :=
  fun u =>
    (E.symm.toContinuousLinearMap.comp ((gD (E u)).comp E.toContinuousLinearMap))

/-- **The conjugated map has the conjugated fderiv at every point** (chain rule over the two linear
CLEs `E`, `E.symm` and the middle nonlinear `g`). -/
theorem cleConj_hasFDerivAt (E : (Fin N → ℝ) ≃L[ℝ] W) (g : W → W) (gD : W → W →L[ℝ] W)
    (hg : ∀ w, HasFDerivAt g (gD w) w) (u : Fin N → ℝ) :
    HasFDerivAt (cleConjMap E g) (cleConjDeriv E gD u) u := by
  have hE : HasFDerivAt (E : (Fin N → ℝ) → W) E.toContinuousLinearMap u := E.hasFDerivAt
  have hmid : HasFDerivAt g (gD (E u)) (E u) := hg (E u)
  have hcomp1 : HasFDerivAt (fun x => g (E x)) ((gD (E u)).comp E.toContinuousLinearMap) u :=
    hmid.comp u hE
  have hEsymm : HasFDerivAt (E.symm : W → (Fin N → ℝ)) E.symm.toContinuousLinearMap (g (E u)) :=
    E.symm.hasFDerivAt
  exact hEsymm.comp u hcomp1

/-- **The conjugated factor's abs-det** `= |det (gD (E u))|` (conjugation by a CLE preserves the det,
`det_conj`). -/
theorem cleConj_abs_det [FiniteDimensional ℝ W]
    (E : (Fin N → ℝ) ≃L[ℝ] W) (gD : W → W →L[ℝ] W) (u : Fin N → ℝ) :
    |LinearMap.det (cleConjDeriv E gD u).toLinearMap| = |LinearMap.det (gD (E u)).toLinearMap| := by
  have heq : (cleConjDeriv E gD u).toLinearMap
      = (E.symm.toLinearEquiv : W →ₗ[ℝ] (Fin N → ℝ)) ∘ₗ (gD (E u)).toLinearMap ∘ₗ
          (E.symm.toLinearEquiv.symm : (Fin N → ℝ) →ₗ[ℝ] W) := by
    rfl
  rw [heq, LinearMap.det_conj]

end Generic

/-! ## The `ChartFactor N` packaging -/

variable {N : ℕ} {W : Type*}
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **The whole-space CLE-conjugated `ChartFactor`** — `g` conjugated into the flat ambient via the CLE
`E : (Fin N → ℝ) ≃L[ℝ] W`. -/
noncomputable def cleConjFactor (E : (Fin N → ℝ) ≃L[ℝ] W) (g : W → W) (gD : W → W →L[ℝ] W)
    (hg : ∀ w, HasFDerivAt g (gD w) w) : ChartFactor N where
  f := cleConjMap E g
  D := cleConjDeriv E gD
  hasD := cleConj_hasFDerivAt E g gD hg

omit [FiniteDimensional ℝ W] in
@[simp] theorem cleConjFactor_f (E : (Fin N → ℝ) ≃L[ℝ] W) (g : W → W) (gD : W → W →L[ℝ] W)
    (hg : ∀ w, HasFDerivAt g (gD w) w) :
    (cleConjFactor E g gD hg).f = cleConjMap E g := rfl

omit [FiniteDimensional ℝ W] in
@[simp] theorem cleConjFactor_D (E : (Fin N → ℝ) ≃L[ℝ] W) (g : W → W) (gD : W → W →L[ℝ] W)
    (hg : ∀ w, HasFDerivAt g (gD w) w) :
    (cleConjFactor E g gD hg).D = cleConjDeriv E gD := rfl

/-- **The conjugated factor's abs-det** (`ChartFactor` form): `= |det (gD (E u))|`. -/
theorem cleConjFactor_abs_det (E : (Fin N → ℝ) ≃L[ℝ] W) (g : W → W) (gD : W → W →L[ℝ] W)
    (hg : ∀ w, HasFDerivAt g (gD w) w) (u : Fin N → ℝ) :
    |LinearMap.det ((cleConjFactor E g gD hg).D u).toLinearMap| = |LinearMap.det (gD (E u)).toLinearMap| :=
  cleConj_abs_det E gD u

/-! ## The composite of whole-space conjugated factors collapses to ONE conjugation

If every factor in `fs` is `cleConjFactor E gᵢ …` with the SAME CLE `E` (i.e. each `.f = cleConjMap E
gᵢ`), then `composeFold fs = E.symm ∘ (g₀ ∘ … ∘ g_{n−1}) ∘ E` — the conjugation telescopes (the inner
`E ∘ E.symm` at each seam cancels). This is the OPTION-1 payoff: the bridge `composeFold fs =
paramsEquivFlat ∘ Φ` reduces to the `Params`-level `(g-composite) = Φ ∘ E.symm`.

The statement is over the underlying maps `gs : List (W → W)`: if `fs` and `gs` line up factor-by-factor
(`(fs.get i).f = cleConjMap E (gs.get i)`), the composite collapses. We phrase it with a per-element
hypothesis `hfs : fs.map (·.f) = gs.map (cleConjMap E ·)`. -/

omit [FiniteDimensional ℝ W] in
/-- The composite of factors whose maps are all `cleConjMap E gᵢ` (same `E`) collapses to
`E.symm ∘ (foldr (· ∘ ·) id gs) ∘ E`. The `E ∘ E.symm` at each seam cancels. -/
theorem composeFold_eq_cleConj_foldr (E : (Fin N → ℝ) ≃L[ℝ] W)
    (fs : List (ChartFactor N)) (gs : List (W → W))
    (hfs : fs.map (·.f) = gs.map (cleConjMap E)) :
    composeFold fs = fun u => E.symm ((gs.foldr (· ∘ ·) id) (E u)) := by
  induction fs generalizing gs with
  | nil =>
      cases gs with
      | nil => funext u; simp [composeFold, ContinuousLinearEquiv.symm_apply_apply]
      | cons g rest => simp at hfs
  | cons F fsrest ih =>
      cases gs with
      | nil => simp at hfs
      | cons g grest =>
          simp only [List.map_cons, List.cons.injEq] at hfs
          obtain ⟨hF, hrest⟩ := hfs
          funext u
          rw [composeFold_cons, Function.comp_apply, ih grest hrest]
          simp only [List.foldr_cons, Function.comp_apply]
          rw [show F.f = cleConjMap E g from hF, cleConjMap,
            ContinuousLinearEquiv.apply_symm_apply]

end DLNFibre.DLN.RLCT
