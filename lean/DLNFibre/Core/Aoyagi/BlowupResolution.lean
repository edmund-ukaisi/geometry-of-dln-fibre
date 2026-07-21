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

/-- The blow-up chart's Jacobian determinant is `wᵢ`: `jacDet (blowupMap2 i) w = w i`. -/
theorem jacDet_blowupMap2 (i : Fin 2) (w : Fin 2 → ℝ) :
    jacDet (blowupMap2 i) w = w i := by
  unfold jacDet
  rw [(hasFDerivAt_blowupMap2 i w).fderiv,
      ← LinearMap.det_toMatrix' (blowupDeriv2 i w).toLinearMap, Matrix.det_fin_two]
  fin_cases i <;> simp [LinearMap.toMatrix'_apply, blowupDeriv2]

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
theorem volume_blowup_excep2 (i : Fin 2) :
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
theorem monomialFam_blowup_bexp2 (i : Fin 2) (w : Fin 2 → ℝ) :
    monomialFam (fun (_ : Fin 1) (j : Fin 2) ↦ if j = i then 1 else 0) 0 w = w i := by
  fin_cases i <;> simp [monomialFam]

/-- The Jacobian weight of the exponent `jac j = [j = i]` is `|wᵢ|`. -/
theorem jacWeight_blowup_jac2 (i : Fin 2) (w : Fin 2 → ℝ) :
    jacWeight (fun j : Fin 2 ↦ if j = i then 1 else 0) w = |w i| := by
  fin_cases i <;> simp [jacWeight]

/-! ## The blow-up chart -/

/-- **The pivot-`i` blow-up chart** of the coordinate family `F = (u₀, u₁)`. A genuine
non-identity resolution chart (`g = blowupMap2 i`, analytic, `|det Dg| = |wᵢ|`, ideal identity
`⟨u₀∘g, u₁∘g⟩ = ⟨wᵢ⟩` both ways with polynomial cofactors). -/
noncomputable def blowupChart2 (i : Fin 2) : Chart coordFam2 (0 : Fin 2 → ℝ) where
  g := blowupMap2 i
  hg0 := blowupMap2_zero i
  hg_cont := continuous_blowupMap2 i
  hg_analytic := analyticOnNhd_blowupMap2 i
  hFmeas := fun k ↦ measurable_pi_apply k
  dom := Metric.closedBall 0 1
  hdom_compact := isCompact_closedBall 0 1
  hdom_zero := Metric.mem_closedBall_self (by norm_num)
  nbhd := Set.univ
  hnbhd_open := isOpen_univ
  hdom_sub := Set.subset_univ _
  excep := {w | w i = 0}
  hexcep_meas := by
    have : {w : Fin 2 → ℝ | w i = 0} = (fun w ↦ w i) ⁻¹' {0} := rfl
    rw [this]; exact (measurable_pi_apply i) (measurableSet_singleton 0)
  hexcep_null := volume_blowup_excep2 i
  hg_inj := injOn_blowupMap2 i
  M' := 1
  bexp := fun _ j ↦ if j = i then 1 else 0
  k₀ := 0
  hchain := fun k d ↦ by fin_cases k; exact le_refl _
  hbind := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simp⟩⟩
  hunit_mult := by
    intro d hd
    rw [bindingAxes, Finset.mem_filter] at hd
    by_cases hd2 : d = i
    · simp [hd2]
    · simp [hd2] at hd
  jac := fun j ↦ if j = i then 1 else 0
  unit := fun _ ↦ 1
  hunit_cont := continuousOn_const
  hunit_ne := fun _ _ ↦ one_ne_zero
  hjac := by
    intro u _
    rw [jacDet_blowupMap2, jacWeight_blowup_jac2, abs_one, mul_one]
  hideal_fwd := by
    refine ⟨fun k _ u ↦ if k = i then 1 else u k, ?_, ?_⟩
    · intro k _
      by_cases hk : k = i
      · simp only [hk, if_pos]; exact continuousOn_const
      · simp only [if_neg hk]; exact (continuous_apply k).continuousOn
    · intro u _ k
      rw [Fin.sum_univ_one, monomialFam_blowup_bexp2]
      by_cases hk : k = i <;>
        simp [coordFam2, blowupMap2, Function.comp, hk, mul_comm]
  hideal_bwd := by
    refine ⟨fun _ k u ↦ if k = i then 1 else 0, ?_, ?_⟩
    · intro _ _; exact continuousOn_const
    · intro u _ k
      obtain rfl : k = 0 := Fin.fin_one_eq_zero k
      fin_cases i <;>
        simp [monomialFam, coordFam2, blowupMap2, Function.comp, Fin.sum_univ_two]

/-! ## The two-chart max-pivot cover of a box -/

/-- **The exact max-pivot cover.** The open unit ball is covered by the images of the two blow-up
charts' unit boxes: at any point the coordinate of maximal absolute value is the pivot. -/
theorem ball_subset_iUnion_blowup2_image :
    Metric.ball (0 : Fin 2 → ℝ) 1 ⊆
      ⋃ i : Fin 2, (blowupMap2 i) '' (Metric.closedBall 0 1) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos] at hw
  have hw0 : |w 0| < 1 := by have := hw 0; rwa [Real.norm_eq_abs] at this
  have hw1 : |w 1| < 1 := by have := hw 1; rwa [Real.norm_eq_abs] at this
  rw [Set.mem_iUnion]
  -- select the pivot: whichever of |w 0|, |w 1| is larger.
  rcases le_total (|w 1|) (|w 0|) with hle | hle
  · -- pivot 0
    refine ⟨0, ?_⟩
    by_cases hw00 : w 0 = 0
    · have hw10 : w 1 = 0 := by
        have : |w 1| ≤ 0 := by rw [hw00, abs_zero] at hle; exact hle
        simpa using abs_nonpos_iff.mp this
      refine ⟨0, Metric.mem_closedBall_self (by norm_num), ?_⟩
      funext j; fin_cases j <;> simp [blowupMap2, hw00, hw10]
    · refine ⟨![w 0, w 1 / w 0], ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num),
          Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · simp only [Real.norm_eq_abs, Matrix.cons_val_zero]; exact hw0.le
        · simp only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero, abs_div]
          exact (div_le_one (abs_pos.mpr hw00)).mpr hle
      · funext j
        fin_cases j <;>
          simp [blowupMap2, mul_div_cancel₀, hw00]
  · -- pivot 1
    refine ⟨1, ?_⟩
    by_cases hw10 : w 1 = 0
    · have hw00 : w 0 = 0 := by
        have : |w 0| ≤ 0 := by rw [hw10, abs_zero] at hle; exact hle
        simpa using abs_nonpos_iff.mp this
      refine ⟨0, Metric.mem_closedBall_self (by norm_num), ?_⟩
      funext j; fin_cases j <;> simp [blowupMap2, hw00, hw10]
    · refine ⟨![w 0 / w 1, w 1], ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num),
          Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · simp only [Real.norm_eq_abs, Matrix.cons_val_zero, abs_div]
          exact (div_le_one (abs_pos.mpr hw10)).mpr hle
        · simp only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero]; exact hw1.le
      · funext j
        fin_cases j <;>
          simp [blowupMap2, mul_div_cancel₀, hw10]

/-! ## The blow-up resolution -/

/-- **The origin blow-up as a `Resolution`.** Two `blowupChart2` charts whose unit-box images
exactly cover the open unit ball — a genuine (non-identity) inhabitation of `Resolution` resolving
the non-principal maximal ideal `⟨u₀, u₁⟩`. -/
noncomputable def blowupResolution2 : Resolution coordFam2 (0 : Fin 2 → ℝ) where
  numCharts := 2
  charts := blowupChart2
  hne := Finset.univ_nonempty
  U := Metric.ball 0 1
  hU := Metric.ball_mem_nhds 0 one_pos
  hcover := by
    have hsub : Metric.ball (0 : Fin 2 → ℝ) 1 ⊆
        ⋃ c : Fin 2, (blowupChart2 c).g '' (blowupChart2 c).dom :=
      ball_subset_iUnion_blowup2_image
    rw [Set.diff_eq_empty.2 hsub]
    exact measure_empty

end DLNFibre.Core.Aoyagi
