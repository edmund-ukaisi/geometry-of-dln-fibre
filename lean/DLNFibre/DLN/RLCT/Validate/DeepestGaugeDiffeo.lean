import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGaugeDiffeo` — the IFT local-diffeo det-bound bedrock (#44c)

The **analytic core** of the gauge-absorption RLCT peels (`regAbsorb_rlct` / `coreAbsorb_rlct`,
g161): the bounded-unit-Jacobian data that crux2's `rlctAtOn_boundedUnit_localHomeomorph` (#72)
consumes, derived from the CLEAN local-diffeo form a `ContDiffAt` map with an invertible derivative
at the basepoint provides (the implicit-function-theorem output, `ContDiffAt.toOpenPartialHomeomorph`).

This module is **structure-independent** (Mathlib-only): it discharges #72's `hderiv` / `hdetmeas` /
`hbdd` hypotheses for the Jacobian `w ↦ fderiv ℝ f w` of any `C¹` self-map `f` with
`HasFDerivAt f (f' : ≃L) wstar`. Both gauge absorptions (raw-regular ↦ `E`, raw-core ↦ Schur `S_s`)
are local diffeos of this form (g161: the residual map `E` has `dE(wstar)` an iso onto the regular
directions), so each peel = #72 applied to this data.

## The det-bound mechanism (the content crux2 offered to pair on)

For a `ContDiffAt ℝ 1 f wstar` with `HasFDerivAt f (f' : M ≃L[ℝ] M) wstar`:
- `w ↦ fderiv ℝ f w` is `ContinuousAt wstar` (`ContDiffAt.continuousAt_fderiv`);
- `g ↦ g.det` is `Continuous` (`ContinuousLinearMap.continuous_det`), so `w ↦ |（fderiv ℝ f w).det|`
  is `ContinuousAt wstar`;
- at `wstar` the value is `|f'.det| > 0` (a `≃L` has unit determinant: `HasFDerivAt.fderiv` +
  `LinearEquiv.isUnit_det`);
- `ContinuousAt` + positive value ⟹ on an open nbhd `V ∋ wstar`, `|det| ∈ [a, b]` with
  `a = |f'.det|/2 > 0` — the `hbdd` bounded-unit datum.
-/

open scoped Topology
open Filter

namespace DLNFibre.DLN.RLCT

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

omit [FiniteDimensional ℝ M] in
/-- The determinant of a continuous-linear-equiv (coerced to a continuous linear map) is nonzero:
its underlying `LinearEquiv` has a unit determinant, and a unit in `ℝ` is nonzero. -/
theorem clm_det_ne_zero (f' : M ≃L[ℝ] M) : (f' : M →L[ℝ] M).det ≠ 0 := by
  change LinearMap.det ((f' : M →L[ℝ] M) : M →ₗ[ℝ] M) ≠ 0
  have he : ((f' : M →L[ℝ] M) : M →ₗ[ℝ] M) = (f'.toLinearEquiv : M →ₗ[ℝ] M) := rfl
  rw [he]
  exact f'.toLinearEquiv.isUnit_det'.ne_zero

omit [FiniteDimensional ℝ M] in
/-- **The Jacobian-determinant is continuous at the basepoint** for a `C¹` map. For
`ContDiffAt ℝ 1 f wstar`, the map `w ↦ |（fderiv ℝ f w).det|` is `ContinuousAt wstar`
(`ContDiffAt.continuousAt_fderiv` ∘ `ContinuousLinearMap.continuous_det` ∘ `|·|`). -/
theorem continuousAt_abs_fderiv_det {f : M → M} {wstar : M} (hf : ContDiffAt ℝ 1 f wstar) :
    ContinuousAt (fun w => |(fderiv ℝ f w).det|) wstar := by
  have h1 : ContinuousAt (fun w => fderiv ℝ f w) wstar := hf.continuousAt_fderiv (by norm_num)
  have h2 : Continuous fun g : M →L[ℝ] M => g.det := ContinuousLinearMap.continuous_det
  exact (continuous_abs.continuousAt).comp ((h2.continuousAt).comp h1)

/-- **The bounded-unit Jacobian datum** (the `hbdd` of crux2's `rlctAtOn_boundedUnit_localHomeomorph`,
#72), derived from the clean IFT form. For a `C¹` self-map `f` whose derivative at `wstar` is the
continuous-linear-equiv `f'` (`HasFDerivAt f (f' :→L) wstar`), there is an OPEN nbhd `V ∋ wstar` on
which `|（fderiv ℝ f w).det|` is two-sidedly bounded by `0 < a := |f'.det|/2` and `b := |f'.det| + 1`.

Mechanism: `|det|` is `ContinuousAt wstar` (`continuousAt_abs_fderiv_det`) with value `|f'.det| > 0`
(`HasFDerivAt.fderiv` rewrites `fderiv f wstar = f'`; `clm_det_ne_zero`). `ContinuousAt` ⟹ the
preimage of the open interval `(a, b)` is a nbhd of `wstar`; take its interior for the open `V`. -/
theorem boundedUnit_fderiv_det {f : M → M} {wstar : M} {f' : M ≃L[ℝ] M}
    (hf : ContDiffAt ℝ 1 f wstar) (hf' : HasFDerivAt f (f' : M →L[ℝ] M) wstar) :
    ∃ V : Set M, IsOpen V ∧ wstar ∈ V ∧
      ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(fderiv ℝ f w).det| ∧ |(fderiv ℝ f w).det| ≤ b := by
  set d : ℝ := |(f' : M →L[ℝ] M).det| with hd
  have hdpos : 0 < d := abs_pos.mpr (clm_det_ne_zero f')
  -- The value of `|det|` at `wstar` is `d` (since `fderiv f wstar = f'`).
  have hval : (fun w => |(fderiv ℝ f w).det|) wstar = d := by
    change |(fderiv ℝ f wstar).det| = d
    rw [hf'.fderiv, hd]
  have hcont : ContinuousAt (fun w => |(fderiv ℝ f w).det|) wstar := continuousAt_abs_fderiv_det hf
  -- `(d/2, d+1)` is an open interval containing the value `d`; pull it back to an open nbhd.
  have hmem : (fun w => |(fderiv ℝ f w).det|) wstar ∈ Set.Ioo (d / 2) (d + 1) := by
    rw [hval]; constructor <;> linarith
  have hpre : (fun w => |(fderiv ℝ f w).det|) ⁻¹' Set.Ioo (d / 2) (d + 1) ∈ 𝓝 wstar :=
    hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds hmem)
  refine ⟨interior ((fun w => |(fderiv ℝ f w).det|) ⁻¹' Set.Ioo (d / 2) (d + 1)),
    isOpen_interior, mem_interior_iff_mem_nhds.mpr hpre, d / 2, d + 1, by positivity, ?_⟩
  intro w hw
  have hwpre : w ∈ (fun w => |(fderiv ℝ f w).det|) ⁻¹' Set.Ioo (d / 2) (d + 1) :=
    interior_subset hw
  have hw' : (fun w => |(fderiv ℝ f w).det|) w ∈ Set.Ioo (d / 2) (d + 1) := hwpre
  exact ⟨le_of_lt hw'.1, le_of_lt hw'.2⟩

end DLNFibre.DLN.RLCT
