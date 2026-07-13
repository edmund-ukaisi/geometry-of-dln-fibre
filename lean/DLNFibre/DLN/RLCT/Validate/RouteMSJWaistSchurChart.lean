import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJWaistSchurChart` — the (3,2,3) max-pivot Schur sector-CoV prototype

**Thread `genm-sj5-waist` (aoyagi-full Stage 2), the DECISIVE prototype for hole (c) `deeperFlagWaist_finite`
step 2.** The `svd-density-mathlib-recon` verdict: the LITERAL rectangular-SVD / Wishart eigenvalue density
is a HEAVY new-module WALL at Mathlib v4.29 (no Stiefel manifold, no Haar-on-O(s), no Vandermonde density,
no coarea, no eigenvalue-map differentiability). The MODERATE bypass (decorrelated-Codex,
`codex/wall-assessment-answer.md` §3): the **max-pivot Schur-flag change-of-variables** — peel the deep
layer `A₁`'s own corank one direction at a time by a Schur chart ON `A₁`, whose Jacobian is a polynomial
`det(pivot)`-power, feeding the banked general diffeomorphism CoV `MeasureTheory.Function.Jacobian`. This
module CLOSES that bypass's deciding chart (the `(3,2,3)` rank-1 pivot, `s = 2`, `x = z = 3`) end-to-end,
sorry-free — **validating the route is a bounded build, not a wall**.

## The chart (Codex `codex/wall-assessment-answer.md` §3)

`Phi : (p, t₁, t₂, ℓ, w₁, w₂) ↦` the deep layer `A₁ : 2×3`, flattened as `Fin 6`:

    A₁ = [ p     p·t₁        p·t₂      ]
         [ ℓ·p   w₁+ℓ·p·t₁   w₂+ℓ·p·t₂ ]

On the max-pivot sector `{p ≠ 0}` (the top-left pivot of `A₁` invertible), `Phi` is a bijection onto its
image with inverse `t_i = a_{1,i+1}/p, ℓ = a_{21}/p, w_i = a_{2,i+1} − ℓ·a_{1,i+1}`. Its Jacobian is the
LOWER-TRIANGULAR matrix `schurChartJac` with diagonal `(1, p, p, p, 1, 1)`, so

    |det DΦ| = |p|³   (the raw Schur map `rᵢ = p·tᵢ` gives one `|p|` factor per collapsed column, `h₁ = 3`).

## What closes here (all sorry-free)

* **`schurChart_hasFDerivAt`** — `HasFDerivAt Phi (schurChartFDeriv v) v`, the Fréchet derivative as an
  explicit `ContinuousLinearMap.pi` of the component derivatives (via `hasFDerivAt_apply` + `.mul` + `.add`).
* **`schurChart_det`** — `(schurChartFDeriv v).det = (v 0)³` (`|p|³` up to sign), via
  `LinearMap.toMatrix' = schurChartJac` (lower-triangular) + `Matrix.det_of_lowerTriangular`.
* **`schurChart_injOn`** — `Phi` is injective on the max-pivot sector `{p ≠ 0}` (pivot cancellation).
* **`schurChart_cov`** — the change-of-variables headline: for every `g`,
  `∫⁻ y in Phi '' {p≠0}, g y = ∫⁻ v in {p≠0}, ENNReal.ofReal (|v 0|³) · g (Phi v)`,
  from the banked `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` fed the Jacobian above.

## Route status

DECISIVE TEST PASSED: the `(3,2,3)` sector chart is ONE ordinary `MeasureTheory.Function.Jacobian` CoV
with a `det = p³` Jacobian, needing NO new general measure theory — so step 2 of the waist SVD-qPeel is
MODERATE (bounded), not the SVD-density wall. Next (post-checkpoint): generalize the pivot dimension to the
`(x, s, z)`/`s ≥ 2` flag recursion, thread the DECORATED integral, and compose with the banked
`qPeelIntegral_lt_top` + `waistCharge_eq_minAdm` (charge tightness). UNTRACKED, NOT wired into
`DLNFibre.lean`/`AxCheck` — the canonical library stays 0-sorry.
-/

namespace DLNFibre.DLN.RLCT.WaistSchurChart

open MeasureTheory Matrix ContinuousLinearMap

noncomputable section

/-- Coordinate projection `(Fin 6 → ℝ) →L[ℝ] ℝ`, typed to fix instance inference. -/
abbrev P (i : Fin 6) : (Fin 6 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

/-- The `(3,2,3)` max-pivot Schur chart: params `(p,t₁,t₂,ℓ,w₁,w₂)` ↦ the deep layer `A₁` (2×3), flattened
as `Fin 6` in the order `(a₁₁,a₁₂,a₁₃,a₂₁,a₂₂,a₂₃)`. -/
def Phi (v : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![v 0, v 0 * v 1, v 0 * v 2, v 3 * v 0, v 4 + v 3 * v 0 * v 1, v 5 + v 3 * v 0 * v 2]

/-- The Fréchet derivative of `Phi` at `v`, as an explicit `pi` of component functionals (matching the
`HasFDerivAt.mul`/`.add` outputs). Its matrix is `schurChartJac`, lower-triangular with diagonal
`(1,p,p,p,1,1)`. -/
def schurChartFDeriv (v : Fin 6 → ℝ) : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℝ) :=
  ContinuousLinearMap.pi ![
    P 0, v 0 • P 1 + v 1 • P 0, v 0 • P 2 + v 2 • P 0, v 3 • P 0 + v 0 • P 3,
    P 4 + ((v 3 * v 0) • P 1 + v 1 • (v 3 • P 0 + v 0 • P 3)),
    P 5 + ((v 3 * v 0) • P 2 + v 2 • (v 3 • P 0 + v 0 • P 3))]

/-- The lower-triangular Jacobian matrix of `Phi` (diagonal `1,p,p,p,1,1`), so `det = p³`. -/
def schurChartJac (v : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![ (1:ℝ), 0, 0, 0, 0, 0; v 1, v 0, 0, 0, 0, 0; v 2, 0, v 0, 0, 0, 0;
      v 3, 0, 0, v 0, 0, 0; v 3 * v 1, v 3 * v 0, 0, v 0 * v 1, 1, 0;
      v 3 * v 2, 0, v 3 * v 0, v 0 * v 2, 0, 1]

/-- **`Phi` has Fréchet derivative `schurChartFDeriv v` at `v`** — component-wise via the coordinate
projections' derivatives, products (`HasFDerivAt.mul`), and sums (`.add`). -/
lemma schurChart_hasFDerivAt (v : Fin 6 → ℝ) : HasFDerivAt Phi (schurChartFDeriv v) v := by
  refine hasFDerivAt_pi.mpr (fun i => ?_)
  fin_cases i
  · exact hasFDerivAt_apply 0 v
  · exact (hasFDerivAt_apply 0 v).mul (hasFDerivAt_apply 1 v)
  · exact (hasFDerivAt_apply 0 v).mul (hasFDerivAt_apply 2 v)
  · exact (hasFDerivAt_apply 3 v).mul (hasFDerivAt_apply 0 v)
  · exact (hasFDerivAt_apply 4 v).add
      (((hasFDerivAt_apply 3 v).mul (hasFDerivAt_apply 0 v)).mul (hasFDerivAt_apply 1 v))
  · exact (hasFDerivAt_apply 5 v).add
      (((hasFDerivAt_apply 3 v).mul (hasFDerivAt_apply 0 v)).mul (hasFDerivAt_apply 2 v))

set_option maxHeartbeats 1200000 in
/-- **The derivative's matrix is `schurChartJac v`** (lower-triangular). -/
lemma toMatrix_schurChartFDeriv (v : Fin 6 → ℝ) :
    LinearMap.toMatrix' (schurChartFDeriv v).toLinearMap = schurChartJac v := by
  ext i j
  rw [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, schurChartFDeriv]
  fin_cases i <;> fin_cases j <;>
    simp only [ContinuousLinearMap.pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, P,
      ContinuousLinearMap.proj_apply, schurChartJac, Matrix.of_apply] <;>
    (try norm_num [Pi.single_apply, Fin.ext_iff]) <;> (try ring)

set_option maxHeartbeats 1200000 in
/-- **The Schur chart Jacobian determinant is `p³`** (`= (v 0)³`), via the lower-triangular matrix. -/
lemma schurChart_det (v : Fin 6 → ℝ) : (schurChartFDeriv v).det = (v 0) ^ 3 := by
  have hdet : LinearMap.det (schurChartFDeriv v).toLinearMap
      = (LinearMap.toMatrix' (schurChartFDeriv v).toLinearMap).det := by
    rw [← LinearMap.det_toLin' (LinearMap.toMatrix' (schurChartFDeriv v).toLinearMap),
      Matrix.toLin'_toMatrix']
  rw [ContinuousLinearMap.det, hdet, toMatrix_schurChartFDeriv, Matrix.det_of_lowerTriangular]
  · simp [schurChartJac, Fin.prod_univ_succ]; ring
  · intro a b hab
    simp only [OrderDual.toDual_lt_toDual] at hab
    fin_cases a <;> fin_cases b <;> simp_all [schurChartJac]

/-- **`Phi` is injective on the max-pivot sector `{p ≠ 0}`** — recover `p` from `a₁₁`, then `t,ℓ,w` by
pivot cancellation. -/
lemma schurChart_injOn : Set.InjOn Phi {v : Fin 6 → ℝ | v 0 ≠ 0} := by
  intro u hu w _ h
  simp only [Set.mem_setOf_eq] at hu
  have e0 : u 0 = w 0 := congrFun h 0
  have e1 : u 0 * u 1 = w 0 * w 1 := congrFun h 1
  have e2 : u 0 * u 2 = w 0 * w 2 := congrFun h 2
  have e3 : u 3 * u 0 = w 3 * w 0 := congrFun h 3
  have e4 : u 4 + u 3 * u 0 * u 1 = w 4 + w 3 * w 0 * w 1 := congrFun h 4
  have e5 : u 5 + u 3 * u 0 * u 2 = w 5 + w 3 * w 0 * w 2 := congrFun h 5
  have h1 : u 1 = w 1 := by rw [← e0] at e1; exact mul_left_cancel₀ hu e1
  have h2 : u 2 = w 2 := by rw [← e0] at e2; exact mul_left_cancel₀ hu e2
  have h3 : u 3 = w 3 := by rw [← e0] at e3; exact mul_right_cancel₀ hu e3
  have h4 : u 4 = w 4 := by rw [← e0, ← h1, ← h3] at e4; linarith
  have h5 : u 5 = w 5 := by rw [← e0, ← h2, ← h3] at e5; linarith
  funext i; fin_cases i <;> assumption

/-- **The (3,2,3) max-pivot Schur sector change-of-variables (the DECISIVE prototype, `|det| = |p|³`).**
For every `g`, the deep-layer integral over the image of the max-pivot sector equals the parameter
integral weighted by the polynomial Jacobian `|p|³`. One ordinary `MeasureTheory.Function.Jacobian` CoV —
no SVD/Wishart density, no Stiefel/Haar — validating the waist step-2 bypass as bounded, not a wall. -/
theorem schurChart_cov (g : (Fin 6 → ℝ) → ENNReal) :
    ∫⁻ y in Phi '' {v : Fin 6 → ℝ | v 0 ≠ 0}, g y
      = ∫⁻ v in {v : Fin 6 → ℝ | v 0 ≠ 0}, ENNReal.ofReal (|v 0| ^ 3) * g (Phi v) := by
  have hmeas : MeasurableSet {v : Fin 6 → ℝ | v 0 ≠ 0} := by
    have hset : {v : Fin 6 → ℝ | v 0 ≠ 0} = (fun v : Fin 6 → ℝ => v 0) ⁻¹' {0}ᶜ := by
      ext v; simp [Set.mem_preimage]
    rw [hset]; exact (measurable_pi_apply 0) (measurableSet_singleton (0:ℝ)).compl
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas
      (fun v _ => (schurChart_hasFDerivAt v).hasFDerivWithinAt) schurChart_injOn g]
  refine setLIntegral_congr_fun hmeas (fun v _ => ?_)
  rw [schurChart_det v, abs_pow]

end

end DLNFibre.DLN.RLCT.WaistSchurChart
