import DLNFibre.Core.Aoyagi.ResolutionInhabited

/-!
# `Core.Aoyagi.OriginBlowup` — leaf-2: the general-`Fin D` origin blow-up

The reusable coordinate-centre blow-up atom (Codex leaf-2), over a GENERAL ambient dimension
`Fin D`: the `D`-chart resolution of the coordinate family `F = (u₀,…,u_{D-1})` (`∑Fᵢ² = ‖u‖²`,
the maximal-ideal singularity). The universal Jacobian det `jacDet (blowupMap i) w = (w i)^(D-1)`
is proven for ALL `D`, so it INSTANTIATES at any dimension (e.g. `D = flatDim d`) with no
opaque-width `fin_cases`. This is the shared atom rung (B) and the monument's blow-up step need.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- The origin blow-up chart map with pivot `i`: slot `i ↦ wᵢ`, slot `j ≠ i ↦ wᵢ·wⱼ`. -/
def blowupMap (i : Fin D) : (Fin D → ℝ) → (Fin D → ℝ) :=
  fun w j ↦ if j = i then w i else w i * w j

/-- The Jacobian `ContinuousLinearMap` of `blowupMap i` at `w`. -/
noncomputable def blowupDeriv (i : Fin D) (w : Fin D → ℝ) :
    (Fin D → ℝ) →L[ℝ] (Fin D → ℝ) :=
  ContinuousLinearMap.pi (fun j ↦ if j = i then ContinuousLinearMap.proj i
    else (w i) • ContinuousLinearMap.proj j + (w j) • ContinuousLinearMap.proj i)

theorem hasFDerivAt_blowupMap (i : Fin D) (w : Fin D → ℝ) :
    HasFDerivAt (blowupMap i) (blowupDeriv i w) w := by
  rw [blowupDeriv, hasFDerivAt_pi]
  intro j
  by_cases hj : j = i
  · have hf : (fun w : Fin D → ℝ ↦ blowupMap i w j) = fun w ↦ w i := by
      funext w; simp [blowupMap, hj]
    rw [hf, if_pos hj]
    exact hasFDerivAt_apply i w
  · have hf : (fun w : Fin D → ℝ ↦ blowupMap i w j) = fun w ↦ w i * w j := by
      funext w; simp [blowupMap, hj]
    rw [hf, if_neg hj]
    exact (hasFDerivAt_apply i w).mul (hasFDerivAt_apply j w)

/-- The entries of the Jacobian matrix of `blowupMap i` at `w`. -/
theorem toMatrix'_blowupDeriv (i : Fin D) (w : Fin D → ℝ) (a c : Fin D) :
    LinearMap.toMatrix' (blowupDeriv i w).toLinearMap a c =
      if a = i then (if i = c then 1 else 0)
      else (w i * (if a = c then 1 else 0) + w a * (if i = c then 1 else 0)) := by
  rw [LinearMap.toMatrix'_apply]
  by_cases ha : a = i
  · subst ha
    simp [blowupDeriv, Pi.single_apply]
  · simp [blowupDeriv, Pi.single_apply, ha]

/-- **The universal Jacobian determinant** `jacDet (blowupMap i) w = (w i)^(D-1)` (`2 ≤ D`). -/
theorem jacDet_blowupMap (hD : 2 ≤ D) (i : Fin D) (w : Fin D → ℝ) :
    jacDet (blowupMap i) w = (w i) ^ (D - 1) := by
  unfold jacDet
  rw [(hasFDerivAt_blowupMap i w).fderiv, ← LinearMap.det_toMatrix' (blowupDeriv i w).toLinearMap]
  set M := LinearMap.toMatrix' (blowupDeriv i w).toLinearMap with hMdef
  -- block-triangular splitter: pivot row `i` is its own singleton block (`1`); the rest is `wᵢ•I`.
  set b : Fin D → ℕ := fun a ↦ if a = i then 1 else 0 with hb
  have hbt : M.BlockTriangular b := by
    intro a c hlt
    have hai : a = i := by by_contra h; simp [hb, h] at hlt
    have hci : c ≠ i := by rintro rfl; simp [hb, hai] at hlt
    rw [hMdef, toMatrix'_blowupDeriv]
    subst hai
    simp [Ne.symm hci]
  rw [hbt.det]
  -- the image of `b` is `{0, 1}` (some `a ≠ i` exists since `2 ≤ D`).
  obtain ⟨a₀, ha₀⟩ : ∃ a : Fin D, a ≠ i := by
    have : 1 < Fintype.card (Fin D) := by simpa using hD
    obtain ⟨a₀, ha₀⟩ := Fintype.exists_ne_of_one_lt_card this i
    exact ⟨a₀, ha₀⟩
  have himg : Finset.univ.image b = {0, 1} := by
    apply Finset.Subset.antisymm
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨a, rfl⟩ := hx
      by_cases h : a = i <;> simp [hb, h]
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.2 ⟨a₀, Finset.mem_univ _, by simp [hb, ha₀]⟩
      · exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, by simp [hb]⟩
  rw [himg, Finset.prod_pair (by norm_num : (0 : ℕ) ≠ 1)]
  -- the pivot block `{i}` is `[1]`; the residual block is `wᵢ • I` on `{a ≠ i}`.
  have hblk1 : (M.toSquareBlock b 1).det = 1 := by
    have h1 : M.toSquareBlock b 1 = 1 := by
      ext p q
      have hp : (p : Fin D) = i := by
        have := p.2; simp only [hb] at this; by_contra h; simp [h] at this
      have hq : (q : Fin D) = i := by
        have := q.2; simp only [hb] at this; by_contra h; simp [h] at this
      have hpq : p = q := Subtype.ext (hp.trans hq.symm)
      rw [hpq, Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply_eq,
        hMdef, toMatrix'_blowupDeriv, hq]
      simp
    rw [h1, Matrix.det_one]
  have hblk0 : (M.toSquareBlock b 0).det = (w i) ^ (D - 1) := by
    have hEq : M.toSquareBlock b 0 = (w i) • (1 : Matrix _ _ ℝ) := by
      ext p q
      have hp : (p : Fin D) ≠ i := by
        have := p.2; simp only [hb] at this; by_contra h; simp [h] at this
      have hq : (q : Fin D) ≠ i := by
        have := q.2; simp only [hb] at this; by_contra h; simp [h] at this
      rw [Matrix.toSquareBlock_def, Matrix.of_apply, hMdef, toMatrix'_blowupDeriv]
      simp only [hp, if_false, Ne.symm hq, mul_zero, add_zero, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one]
      by_cases hpq : (p : Fin D) = (q : Fin D)
      · rw [if_pos hpq, if_pos (Subtype.ext hpq)]
      · rw [if_neg hpq, if_neg (fun h ↦ hpq (Subtype.ext_iff.1 h))]
    rw [hEq, Matrix.det_smul, Matrix.det_one, mul_one]
    congr 1
    rw [Fintype.card_subtype]
    have hcard : (Finset.univ.filter fun a : Fin D ↦ b a = 0) = Finset.univ.erase i := by
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hb]
      by_cases h : a = i <;> simp [h]
    rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  rw [hblk0, hblk1, mul_one]

/-! ## The remaining chart data (general `Fin D`) -/

/-- The coordinate family over `Fin D`; `∑ (coordFam k)² = ‖u‖²`. -/
def coordFam (D : ℕ) : Fin D → (Fin D → ℝ) → ℝ := fun k u ↦ u k

/-- `blowupMap i` fixes the origin. -/
theorem blowupMap_zero (i : Fin D) : blowupMap i (0 : Fin D → ℝ) = 0 := by
  funext j; simp only [blowupMap, Pi.zero_apply, mul_zero, ite_self]

/-- `blowupMap i` is continuous. -/
theorem continuous_blowupMap (i : Fin D) : Continuous (blowupMap i) := by
  refine continuous_pi (fun j ↦ ?_)
  by_cases hj : j = i
  · have : (fun w : Fin D → ℝ ↦ blowupMap i w j) = fun w ↦ w i := by
      funext w; simp [blowupMap, hj]
    rw [this]; exact continuous_apply i
  · have : (fun w : Fin D → ℝ ↦ blowupMap i w j) = fun w ↦ w i * w j := by
      funext w; simp [blowupMap, hj]
    rw [this]; exact (continuous_apply i).mul (continuous_apply j)

/-- `blowupMap i` is analytic on the whole space (a polynomial map). -/
theorem analyticOnNhd_blowupMap (i : Fin D) :
    AnalyticOnNhd ℝ (blowupMap i) Set.univ := by
  have hproj : ∀ k : Fin D, AnalyticOnNhd ℝ (fun w : Fin D → ℝ ↦ w k) Set.univ := fun k ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin D ↦ ℝ) k).analyticOnNhd _
  apply AnalyticOnNhd.pi
  intro j
  by_cases hj : j = i
  · have : (fun w : Fin D → ℝ ↦ blowupMap i w j) = fun w ↦ w i := by
      funext w; simp [blowupMap, hj]
    rw [this]; exact hproj i
  · have : (fun w : Fin D → ℝ ↦ blowupMap i w j) = fun w ↦ w i * w j := by
      funext w; simp [blowupMap, hj]
    rw [this]; exact (hproj i).mul (hproj j)

/-- The exceptional locus `{wᵢ = 0}` has volume zero (a coordinate hyperplane). -/
theorem volume_blowup_excep (i : Fin D) :
    volume {w : Fin D → ℝ | w i = 0} = 0 := by
  have hset : {w : Fin D → ℝ | w i = 0}
      = {w | MvPolynomial.eval w (MvPolynomial.X i) = 0} := by
    ext w; simp only [Set.mem_setOf_eq, MvPolynomial.eval_X]
  rw [hset]
  exact MvPolynomial.volume_zeroSet_eq_zero _ (MvPolynomial.X_ne_zero i)

/-- `blowupMap i` is injective off the exceptional locus `{wᵢ = 0}`. -/
theorem injOn_blowupMap (i : Fin D) :
    Set.InjOn (blowupMap i) (Set.univ \ {w : Fin D → ℝ | w i = 0}) := by
  intro w hw w' _ heq
  have hwi : w i ≠ 0 := by simpa using hw.2
  have hi : w i = w' i := by
    have := congrFun heq i; simpa [blowupMap] using this
  funext j
  by_cases hj : j = i
  · rw [hj]; exact hi
  · have hprod : w i * w j = w' i * w' j := by
      have := congrFun heq j; simpa [blowupMap, hj] using this
    rw [hi] at hprod
    exact mul_left_cancel₀ (hi ▸ hwi) hprod

/-- The single blow-up monomial `b₁ = wᵢ`. -/
theorem monomialFam_blowup_bexp (i : Fin D) (w : Fin D → ℝ) :
    monomialFam (fun (_ : Fin 1) (j : Fin D) ↦ if j = i then 1 else 0) 0 w = w i := by
  rw [monomialFam, Finset.prod_eq_single i]
  · simp
  · intro d _ hd; simp [hd]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The Jacobian weight of the exponent `jac j = (D-1)·[j = i]` is `|wᵢ|^(D-1)`. -/
theorem jacWeight_blowup_jac (i : Fin D) (w : Fin D → ℝ) :
    jacWeight (fun j : Fin D ↦ if j = i then D - 1 else 0) w = |w i| ^ (D - 1) := by
  rw [jacWeight, Finset.prod_eq_single i]
  · simp
  · intro d _ hd; simp [hd]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## The blow-up chart and the D-chart resolution -/

/-- **The pivot-`i` origin blow-up chart** of the coordinate family over `Fin D` (`2 ≤ D`). -/
noncomputable def blowupChart (hD : 2 ≤ D) (i : Fin D) :
    Chart (coordFam D) (0 : Fin D → ℝ) where
  g := blowupMap i
  hg0 := blowupMap_zero i
  hg_cont := continuous_blowupMap i
  hg_analytic := analyticOnNhd_blowupMap i
  hFmeas := fun k ↦ measurable_pi_apply k
  dom := Metric.closedBall 0 1
  hdom_compact := isCompact_closedBall 0 1
  hdom_zero := Metric.mem_closedBall_self (by norm_num)
  nbhd := Set.univ
  hnbhd_open := isOpen_univ
  hdom_sub := Set.subset_univ _
  excep := {w | w i = 0}
  hexcep_meas := by
    have : {w : Fin D → ℝ | w i = 0} = (fun w ↦ w i) ⁻¹' {0} := rfl
    rw [this]; exact (measurable_pi_apply i) (measurableSet_singleton 0)
  hexcep_null := volume_blowup_excep i
  hg_inj := injOn_blowupMap i
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
  jac := fun j ↦ if j = i then D - 1 else 0
  unit := fun _ ↦ 1
  hunit_cont := continuousOn_const
  hunit_ne := fun _ _ ↦ one_ne_zero
  hjac := by
    intro u _
    rw [jacDet_blowupMap hD, abs_pow, jacWeight_blowup_jac, abs_one, mul_one]
  hideal_fwd := by
    refine ⟨fun k _ u ↦ if k = i then 1 else u k, ?_, ?_⟩
    · intro k _
      by_cases hk : k = i
      · simp only [hk, if_pos]; exact continuousOn_const
      · simp only [if_neg hk]; exact (continuous_apply k).continuousOn
    · intro u _ k
      rw [Fin.sum_univ_one, monomialFam_blowup_bexp]
      by_cases hk : k = i <;> simp [coordFam, blowupMap, Function.comp, hk, mul_comm]
  hideal_bwd := by
    refine ⟨fun _ k u ↦ if k = i then 1 else 0, ?_, ?_⟩
    · intro _ _; exact continuousOn_const
    · intro u _ k
      obtain rfl : k = 0 := Fin.fin_one_eq_zero k
      rw [monomialFam_blowup_bexp,
        Finset.sum_eq_single i (fun j _ hj => by simp [hj])
          (fun h => absurd (Finset.mem_univ i) h)]
      simp [coordFam, blowupMap, Function.comp]

/-- **The exact max-pivot cover** over `Fin D`: the open unit ball is covered by the images of the
`D` charts' unit boxes — at any point the coordinate of maximal absolute value is the pivot. -/
theorem ball_subset_iUnion_blowup_image (hD : 2 ≤ D) :
    Metric.ball (0 : Fin D → ℝ) 1 ⊆
      ⋃ i : Fin D, (blowupMap i) '' (Metric.closedBall 0 1) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos] at hw
  haveI : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  have hne : (Finset.univ : Finset (Fin D)).Nonempty := Finset.univ_nonempty
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ |w j|) hne
  have hwi1 : |w i| ≤ 1 := by have h := hw i; rw [Real.norm_eq_abs] at h; exact h.le
  rw [Set.mem_iUnion]
  refine ⟨i, ?_⟩
  by_cases hwi : w i = 0
  · have hw0 : w = 0 := by
      funext j
      have hj := hi j (Finset.mem_univ j)
      rw [hwi, abs_zero] at hj
      simpa using abs_nonpos_iff.mp hj
    exact ⟨0, Metric.mem_closedBall_self (by norm_num), by rw [hw0, blowupMap_zero]⟩
  · refine ⟨fun j ↦ if j = i then w i else w j / w i, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      rw [Real.norm_eq_abs]
      by_cases hj : j = i
      · rw [hj]; simpa using hwi1
      · simp only [if_neg hj, abs_div]
        rw [div_le_one (abs_pos.mpr hwi)]; exact hi j (Finset.mem_univ j)
    · funext j
      by_cases hj : j = i <;> simp [blowupMap, hj, mul_div_cancel₀, hwi]

/-- **The origin blow-up as a `Resolution`** over `Fin D` (`2 ≤ D`): the `D`-chart max-pivot atlas
resolving the maximal-ideal singularity `⟨u₀,…,u_{D-1}⟩`. -/
noncomputable def blowupResolution (hD : 2 ≤ D) : Resolution (coordFam D) (0 : Fin D → ℝ) where
  numCharts := D
  charts := blowupChart hD
  hne := by haveI : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩; exact Finset.univ_nonempty
  U := Metric.ball 0 1
  hU := Metric.ball_mem_nhds 0 one_pos
  hcover := by
    have hsub : Metric.ball (0 : Fin D → ℝ) 1 ⊆
        ⋃ c : Fin D, (blowupChart hD c).g '' (blowupChart hD c).dom :=
      ball_subset_iUnion_blowup_image hD
    rw [Set.diff_eq_empty.2 hsub]
    exact measure_empty

end DLNFibre.Core.Aoyagi
