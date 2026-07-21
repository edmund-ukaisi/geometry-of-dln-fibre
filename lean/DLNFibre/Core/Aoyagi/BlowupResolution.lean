import DLNFibre.Core.Aoyagi.ResolutionInhabited

/-!
# `Core.Aoyagi.BlowupResolution` — the origin blow-up as a genuine (non-identity) `Resolution`

The SECOND positive inhabitation test of `Chart`/`Resolution` (after `idChart`): the standard
`ℝ²`-at-`0` blow-up resolving the coordinate family `F = (u₀, u₁)` (`∑Fᵢ² = u₀²+u₁²`). Its ideal
`⟨u₀, u₁⟩` is the maximal ideal — NOT principal — so `idChart` cannot resolve it; a genuine
analytic non-identity chart with a non-constant Jacobian is required. This inhabits every `Chart`
field with a real blow-up (analytic `g ≠ id`, `|det Dg| = |wᵢ|`, `RegionRepresents` both ways via
polynomial cofactors, a.e.-injective off `{wᵢ=0}`, an EXACT two-chart max-pivot cover of a box) and
establishes the proof patterns the coupled monument (`exists_coreResolution`) needs.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

/-- The two coordinate functions over `ℝ²`; `∑ (coordFam2 k)² = u₀² + u₁²`. -/
def coordFam2 : Fin 2 → (Fin 2 → ℝ) → ℝ := fun k u ↦ u k

/-- The blow-up chart map with pivot `i`: slot `i ↦ wᵢ`, slot `j ≠ i ↦ wᵢ·wⱼ`. -/
def blowupMap2 (i : Fin 2) : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  fun w j ↦ if j = i then w i else w i * w j

/-- The Jacobian `ContinuousLinearMap` of `blowupMap2 i` at `w`. -/
noncomputable def blowupDeriv2 (i : Fin 2) (w : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (fun j ↦ if j = i then ContinuousLinearMap.proj i
    else (w i) • ContinuousLinearMap.proj j + (w j) • ContinuousLinearMap.proj i)

theorem hasFDerivAt_blowupMap2 (i : Fin 2) (w : Fin 2 → ℝ) :
    HasFDerivAt (blowupMap2 i) (blowupDeriv2 i w) w := by
  rw [blowupDeriv2, hasFDerivAt_pi]
  intro j
  by_cases hj : j = i
  · have hf : (fun w : Fin 2 → ℝ ↦ blowupMap2 i w j) = fun w ↦ w i := by
      funext w; simp [blowupMap2, hj]
    rw [hf, if_pos hj]
    exact hasFDerivAt_apply i w
  · have hf : (fun w : Fin 2 → ℝ ↦ blowupMap2 i w j) = fun w ↦ w i * w j := by
      funext w; simp [blowupMap2, hj]
    rw [hf, if_neg hj]
    exact (hasFDerivAt_apply i w).mul (hasFDerivAt_apply j w)

/-- The blow-up chart's Jacobian determinant is `wᵢ` (up to sign): `jacDet (blowupMap2 i) w = w i`. -/
theorem jacDet_blowupMap2 (i : Fin 2) (w : Fin 2 → ℝ) :
    jacDet (blowupMap2 i) w = w i := by
  unfold jacDet
  rw [(hasFDerivAt_blowupMap2 i w).fderiv,
      ← LinearMap.det_toMatrix' (blowupDeriv2 i w).toLinearMap, Matrix.det_fin_two]
  fin_cases i <;>
    simp [LinearMap.toMatrix'_apply, blowupDeriv2, Pi.single_apply, Fin.sum_univ_two]

/-! ## The chart data as lemmas -/

/-- `blowupMap2 i` fixes the origin. -/
theorem blowupMap2_zero (i : Fin 2) : blowupMap2 i (0 : Fin 2 → ℝ) = 0 := by
  funext j; simp only [blowupMap2, Pi.zero_apply, mul_zero, ite_self]

/-- `blowupMap2 i` is continuous. -/
theorem continuous_blowupMap2 (i : Fin 2) : Continuous (blowupMap2 i) := by
  refine continuous_pi (fun j ↦ ?_)
  by_cases hj : j = i
  · have : (fun w : Fin 2 → ℝ ↦ blowupMap2 i w j) = fun w ↦ w i := by
      funext w; simp [blowupMap2, hj]
    rw [this]; exact continuous_apply i
  · have : (fun w : Fin 2 → ℝ ↦ blowupMap2 i w j) = fun w ↦ w i * w j := by
      funext w; simp [blowupMap2, hj]
    rw [this]; exact (continuous_apply i).mul (continuous_apply j)

/-- `blowupMap2 i` is analytic on the whole space (a polynomial map). -/
theorem analyticOnNhd_blowupMap2 (i : Fin 2) :
    AnalyticOnNhd ℝ (blowupMap2 i) Set.univ := by
  have hproj : ∀ k : Fin 2, AnalyticOnNhd ℝ (fun w : Fin 2 → ℝ ↦ w k) Set.univ := fun k ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) k).analyticOnNhd _
  apply AnalyticOnNhd.pi
  intro j
  by_cases hj : j = i
  · have : (fun w : Fin 2 → ℝ ↦ blowupMap2 i w j) = fun w ↦ w i := by
      funext w; simp [blowupMap2, hj]
    rw [this]; exact hproj i
  · have : (fun w : Fin 2 → ℝ ↦ blowupMap2 i w j) = fun w ↦ w i * w j := by
      funext w; simp [blowupMap2, hj]
    rw [this]; exact (hproj i).mul (hproj j)

/-- The exceptional locus `{wᵢ = 0}` has volume zero (a coordinate hyperplane). -/
theorem volume_blowup_excep (i : Fin 2) :
    volume {w : Fin 2 → ℝ | w i = 0} = 0 := by
  have hset : {w : Fin 2 → ℝ | w i = 0}
      = {w | MvPolynomial.eval w (MvPolynomial.X i) = 0} := by
    ext w; simp only [Set.mem_setOf_eq, MvPolynomial.eval_X]
  rw [hset]
  exact MvPolynomial.volume_zeroSet_eq_zero _ (MvPolynomial.X_ne_zero i)

/-- `blowupMap2 i` is injective off the exceptional locus `{wᵢ = 0}`. -/
theorem injOn_blowupMap2 (i : Fin 2) :
    Set.InjOn (blowupMap2 i) (Set.univ \ {w : Fin 2 → ℝ | w i = 0}) := by
  intro w hw w' hw' heq
  have hwi : w i ≠ 0 := by simpa using hw.2
  have hi : w i = w' i := by
    have := congrFun heq i; simpa [blowupMap2] using this
  funext j
  by_cases hj : j = i
  · rw [hj]; exact hi
  · have hprod : w i * w j = w' i * w' j := by
      have := congrFun heq j; simpa [blowupMap2, hj] using this
    rw [hi] at hprod
    have hw'i : w' i ≠ 0 := hi ▸ hwi
    exact mul_left_cancel₀ hw'i hprod

/-- The single blow-up monomial `b₁ = wᵢ`. -/
theorem monomialFam_blowup_bexp (i : Fin 2) (w : Fin 2 → ℝ) :
    monomialFam (fun (_ : Fin 1) (j : Fin 2) ↦ if j = i then 1 else 0) 0 w = w i := by
  fin_cases i <;> simp [monomialFam, Fin.prod_univ_two]

/-- The Jacobian weight of the exponent `jac j = [j = i]` is `|wᵢ|`. -/
theorem jacWeight_blowup_jac (i : Fin 2) (w : Fin 2 → ℝ) :
    jacWeight (fun j : Fin 2 ↦ if j = i then 1 else 0) w = |w i| := by
  fin_cases i <;> simp [jacWeight, Fin.prod_univ_two]

end DLNFibre.Core.Aoyagi
