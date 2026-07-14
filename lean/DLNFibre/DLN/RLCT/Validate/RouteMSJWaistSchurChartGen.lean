import DLNFibre.DLN.RLCT.Validate.RouteMFactorMaps
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenInjRec
import Mathlib.MeasureTheory.Function.Jacobian

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJWaistSchurChartGen` — the GENERAL max-pivot Schur chart CoV

**Thread `genm-sj5-waist` (aoyagi-full Stage 2), hole (c) `deeperFlagWaist_finite` step 1.** The
DECISIVE `(3,2,3)` prototype `RouteMSJWaistSchurChart.schurChart_cov` (`|det| = |p|³`, one ordinary
`MeasureTheory.Function.Jacobian` CoV) is here GENERALIZED to variable width — the change-of-variables
for the max-pivot Schur chart on a deep-layer block matrix of ANY pivot dimension `t` and residual
shape `(r, c)`.

## The chart (block form)

The banked `schurFrameMap` (`RouteMFactorMaps`) is the Schur frame `S(K,N,X,E) = (K, K·N, (X·K, X·K·N + E))`
on `SchurInc t r c`, with `K : t×t` the pivot block, `N : t×c`, `X : r×t`, `E : r×c`. At `t = 1` this is
EXACTLY the waist deep-layer chart: `K = [p]`, `N = p·t`-row, `X = ℓ·p`-col, `E = w` the residual (Schur
complement) — flattening to `A₁ : (Fin 1 ⊕ Fin r) → (Fin 1 ⊕ Fin c) → ℝ` with pivot `A₁[0][0] = p`.

The banked ingredients (all sorry-free): the differential `schurFrameD` (`schurFrameMap_hasFDerivAt`),
its determinant `|det| = |K.det|^(r+c)` (`schurFrameD_abs_det`, block-triangular — NO variable-width
`fin_cases`), and injectivity when `K` is nonsingular (`schurFrameMap_inj_of_det_ne_zero_gen`).
Conjugated into the flat ambient `Fin N → ℝ` via any CLE `E` (`schurChartFactor`, whose measure space
carries CLEAN pi-Haar instances — no `SchurInc`-product-measure diamond), this yields the CoV headline.

## What lands here (all sorry-free)

* **`schurFrameMap_conj_injOn`** — the conjugated chart `conjBlockMap E schurFrameMap` is injective on
  the max-pivot sector `{u | ((E u).1.1).det ≠ 0}` (E bijective + `schurFrameMap_inj_of_det_ne_zero_gen`).
* **`measurableSet_schurSector`** — the sector is measurable (E continuous, det continuous, `{0}ᶜ`).
* **`schurChartFactor_cov`** — the GENERAL change-of-variables headline: for every `g`,
  `∫⁻ y in chart '' sector, g y = ∫⁻ u in sector, ofReal(|K(u).det|^(r+c)) · g (chart u)`,
  from `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` fed the banked Jacobian. At
  `t = 1` the Jacobian is `|p|^(r+c) = |p|^(s+z)` (the deep-layer waist charge exponent), subsuming
  the `(3,2,3)` prototype's `|p|³`.

UNTRACKED, NOT wired into `DLNFibre.lean`/`AxCheck` — the canonical library stays 0-sorry.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal

variable {t r c N : ℕ} {R : Type*}
  [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]

/-- **The conjugated Schur chart is injective on the max-pivot sector** `{u | ((E u).1.1).det ≠ 0}`.
`conjBlockMap E schurFrameMap u = E.symm (schurFrameMap (E u).1, (E u).2)`; `E` is a bijection and
`schurFrameMap` is injective on `{K.det ≠ 0}` (`schurFrameMap_inj_of_det_ne_zero_gen`), so the block
recovery + `E.injective` give injectivity on the pulled-back sector. -/
theorem schurFrameMap_conj_injOn (E : (Fin N → ℝ) ≃L[ℝ] SchurInc t r c × R) :
    Set.InjOn (conjBlockMap E schurFrameMap) {u : Fin N → ℝ | ((E u).1.1).det ≠ 0} := by
  intro u hu u' _ h
  simp only [Set.mem_setOf_eq] at hu
  -- apply `E` to both sides and unfold the conjugation
  have hE : Prod.map schurFrameMap id (E u) = Prod.map schurFrameMap id (E u') := by
    have := congrArg E h
    simpa only [conjBlockMap, ContinuousLinearEquiv.apply_symm_apply] using this
  rw [Prod.map_apply, Prod.map_apply, Prod.ext_iff, id_eq, id_eq] at hE
  obtain ⟨hg, hrest⟩ := hE
  -- recover the block factor via the banked injectivity, then `E.injective`
  have h1 : (E u).1 = (E u').1 := schurFrameMap_inj_of_det_ne_zero_gen hu hg
  have hEeq : E u = E u' := Prod.ext h1 hrest
  exact E.injective hEeq

/-- **The max-pivot sector is measurable.** `{u | ((E u).1.1).det ≠ 0}` is the preimage under the
continuous `u ↦ ((E u).1.1).det` of `{0}ᶜ`. -/
theorem measurableSet_schurSector (E : (Fin N → ℝ) ≃L[ℝ] SchurInc t r c × R) :
    MeasurableSet {u : Fin N → ℝ | ((E u).1.1).det ≠ 0} := by
  have hcont : Continuous (fun u : Fin N → ℝ => ((E u).1.1).det) := by
    refine Continuous.matrix_det ?_
    exact (continuous_fst.comp (continuous_fst.comp E.continuous))
  have hset : {u : Fin N → ℝ | ((E u).1.1).det ≠ 0}
      = (fun u : Fin N → ℝ => ((E u).1.1).det) ⁻¹' {0}ᶜ := by
    ext u; simp [Set.mem_preimage]
  rw [hset]
  exact hcont.measurable (measurableSet_singleton (0 : ℝ)).compl

/-- **The GENERAL max-pivot Schur chart change-of-variables.** For every `g`, the block-matrix integral
over the image of the max-pivot sector equals the parameter integral weighted by the polynomial Jacobian
`|K.det|^(r+c)`. One ordinary `MeasureTheory.Function.Jacobian` CoV, on the flat ambient `Fin N → ℝ`
(clean pi-Haar instances) via the banked `schurChartFactor` — no variable-width determinant, no
`SchurInc`-product-measure diamond. Generalizes the `(3,2,3)` prototype `schurChart_cov`
(`t=1, r=1, c=2, N=6`, `|det| = |p|³`) to arbitrary `(t, r, c, N)`. -/
theorem schurChartFactor_cov (E : (Fin N → ℝ) ≃L[ℝ] SchurInc t r c × R)
    (g : (Fin N → ℝ) → ℝ≥0∞) :
    ∫⁻ y in (conjBlockMap E schurFrameMap) '' {u : Fin N → ℝ | ((E u).1.1).det ≠ 0}, g y
      = ∫⁻ u in {u : Fin N → ℝ | ((E u).1.1).det ≠ 0},
          ENNReal.ofReal (|((E u).1.1).det| ^ (r + c)) * g (conjBlockMap E schurFrameMap u) := by
  have hS := measurableSet_schurSector E
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
      (f' := conjBlockDeriv E schurFrameD)
      (fun u _ => (conjBlock_hasFDerivAt E schurFrameMap schurFrameD
        (fun b => schurFrameMap_hasFDerivAt b) u).hasFDerivWithinAt)
      (schurFrameMap_conj_injOn E) g]
  refine setLIntegral_congr_fun hS (fun u _ => ?_)
  have hdet : |(conjBlockDeriv E schurFrameD u).det| = |((E u).1.1).det| ^ (r + c) :=
    schurChartFactor_abs_det E u
  rw [hdet]

end DLNFibre.DLN.RLCT
