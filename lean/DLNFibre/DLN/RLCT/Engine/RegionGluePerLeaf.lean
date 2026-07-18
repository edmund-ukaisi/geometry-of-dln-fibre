import DLNFibre.DLN.RLCT.Engine.EngineDefs
import DLNFibre.DLN.RLCT.Validate.RegionGlueModelRead
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# `DLNFibre.DLN.RLCT.Engine.RegionGluePerLeaf` — the per-leaf area-formula read

The engine-facing half of `region_glue`'s per-leaf step: given a leaf `l`'s `ChartBridge` data
(measurable bounded `srcBox`, injective/disjoint `divCoord`/`resCoord`, a.e.-injectivity off a null
set, `LeafPullback`, `LeafJacobian`) and the ratio hypotheses (`c' > 0` below half every terminal
exponent), the box integral over the chart IMAGE is finite:

    ∫⁻ A in l.chartMap '' l.srcBox, ofReal (frobSq (prod M A) ^ (-c')) < ⊤.

Route (elder-ratified fork-8 revision): Mathlib's AREA FORMULA
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) on `srcBox ∖ N̄` (null exceptional fibre
discarded), the `LeafJacobian` upper determinant bound + the `LeafPullback` squeeze reducing the
pulled-back integrand to the monomialised model, then the flat-coordinate `model_read_lt_top`
(`RegionGlueModelRead`) after the measure-preserving transport to `Fin (flatDim M) → ℝ`.

The area formula runs on `Params M` directly, consuming `LeafJacobian`'s `Params`-level derivatives;
this needs `volume` on `Params M` to be an additive Haar measure, supplied here (`Params M` is a
finite-dim normed ℝ-space linearly iso to the flat cube via the banked `paramsEquivFlatCLE`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- `BorelSpace (Params M)` (the pi Borel σ-algebra is the norm-topology Borel one); banked as
`instBorelSpaceParams` in `RouteMSJResolution`, re-exposed here to avoid that heavy import. -/
instance instBorelSpaceParamsGlue (M : Fin (L + 1) → ℕ) : BorelSpace (Params M) :=
  inferInstanceAs (BorelSpace (∀ s : Fin L, Fin (M s.castSucc) → Fin (M s.succ) → ℝ))

/-- **`volume` on `Params M` is an additive Haar measure.** `Params M` is a finite-dim normed
ℝ-space; the banked ℝ-linear iso `paramsEquivFlatCLE` to the flat cube `Fin (flatDim M) → ℝ` (whose
Lebesgue `volume` is Haar) pushes Haar-ness back through `ContinuousLinearEquiv.isAddHaarMeasure_map`,
the measure agreeing by the measure-preserving `paramsEquivFlat`. -/
instance instIsAddHaarMeasureParams (M : Fin (L + 1) → ℕ) :
    (volume : Measure (Params M)).IsAddHaarMeasure := by
  have hsymm : ⇑(paramsEquivFlatCLE M).symm = ⇑(paramsEquivFlat M).symm := by
    funext x
    apply (paramsEquivFlat M).injective
    rw [(paramsEquivFlat M).apply_symm_apply, ← paramsEquivFlatCLE_coe,
      (paramsEquivFlatCLE M).apply_symm_apply]
  have hmap : (volume : Measure (Params M))
      = (volume : Measure (Fin (flatDim M) → ℝ)).map (paramsEquivFlatCLE M).symm := by
    rw [hsymm]
    exact ((measurePreserving_paramsEquivFlat M).symm).map_eq.symm
  rw [hmap]
  infer_instance

/-- **`|det|` is multiplicative over composition** (continuous linear self-maps). The chain-rule
determinant split for the factored chart `chartMap = ψ ∘ β`. -/
theorem abs_det_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E) : |(A.comp B).det| = |A.det| * |B.det| := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp, abs_mul,
    ← ContinuousLinearMap.det, ← ContinuousLinearMap.det]

/-- **`t ↦ t^{-c'}` is antitone on the positives** (`c' > 0`): `0 < a ≤ b ⟹ b^{-c'} ≤ a^{-c'}`. -/
theorem rpow_neg_antitone {a b c' : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc' : 0 < c') :
    b ^ (-c') ≤ a ^ (-c') := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg (ha.trans_le hab).le, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hab hc'.le)

/-- **Flat-cube finiteness of the monomialised leaf model** (the residual base form as an `if`,
matching `residualBaseForm`). `resRank = 0` (bounded unit): the Morse factor is `1`, so the model is
the pure divisor product, reindexed to an all-axis product (`prod_two_family_eq` with empty residual)
and closed by `prod_abs_rpow_cube_lt_top`. `resRank ≥ 1`: exactly `model_read_lt_top`. -/
theorem flat_leaf_model_lt_top {d nd nr : ℕ} (R : ℝ) (hR : 0 < R)
    (dc : Fin nd → Fin d) (rc : Fin nr → Fin d)
    (hdcInj : Function.Injective dc) (hrcInj : Function.Injective rc)
    (hdisj : Disjoint (Set.range dc) (Set.range rc))
    (e : Fin nd → ℝ) (he : ∀ k, -1 < e k)
    (c' : ℝ) (hc' : 0 < c') (hnr : 0 < nr → c' < (nr : ℝ) / 2) :
    ∫⁻ x in cubeBox d R, ENNReal.ofReal ((∏ k, |x (dc k)| ^ (e k))
      * (if nr = 0 then (1 : ℝ) else ∑ i, (x (rc i)) ^ 2) ^ (-c')) < ⊤ := by
  rcases Nat.eq_zero_or_pos nr with h0 | hpos
  · -- bounded unit: the residual factor collapses to `1`
    subst h0
    simp only [reduceIte, Real.one_rpow, mul_one]
    set g : Fin d → ℝ := fun j => ∑ k, if dc k = j then e k else 0 with hgdef
    have hgd : ∀ k₀, g (dc k₀) = e k₀ := fun k₀ => by
      show (∑ k, if dc k = dc k₀ then e k else 0) = e k₀
      rw [Finset.sum_eq_single k₀ (fun k _ hk => if_neg (fun h => hk (hdcInj h)))
          (fun h => absurd (Finset.mem_univ k₀) h), if_pos rfl]
    have hg0 : ∀ j, (∀ k, dc k ≠ j) → g j = 0 := fun j hjd => by
      show (∑ k, if dc k = j then e k else 0) = 0
      exact Finset.sum_eq_zero (fun k _ => if_neg (hjd k))
    have hgpos : ∀ j, -1 < g j := by
      intro j
      by_cases hjd : ∃ k, dc k = j
      · obtain ⟨k, rfl⟩ := hjd; rw [hgd k]; exact he k
      · push_neg at hjd; rw [hg0 j hjd]; norm_num
    have hreindex : ∀ x : Fin d → ℝ, (∏ k, |x (dc k)| ^ (e k)) = ∏ j, |x j| ^ (g j) := fun x => by
      have h := prod_two_family_eq dc rc hdcInj hrcInj hdisj e 0 g hgd (fun i => i.elim0)
        (fun j hjd _ => hg0 j hjd) x
      simpa using h
    rw [setLIntegral_congr_fun (by rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (fun x _ => by rw [hreindex x])]
    exact prod_abs_rpow_cube_lt_top R hR g hgpos
  · simp only [if_neg hpos.ne']
    exact model_read_lt_top R hR hpos dc rc hdcInj hrcInj hdisj e he c' hc' (hnr hpos)

namespace Engine

open DLNFibre.DLN.RLCT

/-- **The per-leaf area-formula read.** Given a leaf's `ChartBridge` data (measurable bounded
`srcBox`, injective/disjoint coordinate maps, a.e.-injectivity off a null set, `LeafPullback`,
`LeafJacobian`) and `0 < c'` below half every terminal exponent, the box integral over the chart
IMAGE is finite. Area formula on `srcBox ∖ N̄` (null fibre discarded), `LeafJacobian` det bound +
`LeafPullback` squeeze → monomial model, measure-preserving transport to the flat cube,
`flat_leaf_model_lt_top`. -/
theorem leaf_chart_image_lintegral_lt_top {M : Fin (L + 1) → ℕ} (l : LeafData (L := L) M)
    (c' : ℝ) (hc' : 0 < c')
    (hsrcM : MeasurableSet l.srcBox)
    (hbdd : ∃ R : ℝ, 0 < R ∧ l.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R)
    (hdcInj : Function.Injective l.divCoord) (hrcInj : Function.Injective l.resCoord)
    (hdisj : Disjoint (Set.range l.divCoord) (Set.range l.resCoord))
    (hnull : ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn l.chartMap (l.srcBox \ N))
    (hlp : LeafPullback l) (hlj : LeafJacobian l)
    (hdivExp : ∀ k, c' < (l.divExp k : ℝ) / 2)
    (hres : 0 < l.resRank → c' < (l.resRank : ℝ) / 2) :
    ∫⁻ A in l.chartMap '' l.srcBox, ENNReal.ofReal (frobSq (prod M A) ^ (-c')) < ⊤ := by
  classical
  rcases l.srcBox.eq_empty_or_nonempty with hE | ⟨w₀, hw₀⟩
  · rw [hE, Set.image_empty]; simp
  obtain ⟨R, hR, hRsub⟩ := hbdd
  obtain ⟨N, hNnull, hInj0⟩ := hnull
  obtain ⟨Nbar, hNsub, hNmeas, hNbarnull⟩ := exists_measurable_superset_of_null hNnull
  have hInj : Set.InjOn l.chartMap (l.srcBox \ Nbar) :=
    hInj0.mono (Set.diff_subset_diff_right hNsub)
  obtain ⟨β, ψ, ψsymm, Dβ, Dψ, loJ, hiJ, hloJ, hchart, hβ, hψ⟩ := hlj
  obtain ⟨rcore, loP, hiP, hloP, hpull⟩ := hlp
  have hhiJ : 0 ≤ hiJ :=
    hloJ.le.trans (((hψ (β w₀) ⟨w₀, hw₀, rfl⟩).2.2.2.1).trans
      (hψ (β w₀) ⟨w₀, hw₀, rfl⟩).2.2.2.2)
  set Dcomp : Params M → (Params M →L[ℝ] Params M) := fun w => (Dψ (β w)).comp (Dβ w) with hDcompdef
  -- `chartMap` has a within-`srcBox` derivative (chain rule on `ψ ∘ β`, congr on `srcBox`)
  have hfd : ∀ w ∈ l.srcBox, HasFDerivWithinAt l.chartMap (Dcomp w) l.srcBox w := by
    intro w hw
    have hcomp : HasFDerivAt (ψ ∘ β) (Dcomp w) w :=
      ((hψ (β w) ⟨w, hw, rfl⟩).2.2.1).comp w (hβ w hw).1
    exact hcomp.hasFDerivWithinAt.congr' (fun w' hw' => hchart w' hw') hw
  -- discard the null exceptional image
  have himg : l.chartMap '' l.srcBox
      = l.chartMap '' (l.srcBox \ Nbar) ∪ l.chartMap '' (l.srcBox ∩ Nbar) := by
    rw [← Set.image_union, Set.diff_union_inter]
  have hnullimg : volume (l.chartMap '' (l.srcBox ∩ Nbar)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun w hw => ((hfd w hw.1).mono Set.inter_subset_left).differentiableWithinAt)
      (measure_mono_null Set.inter_subset_right hNbarnull)
  rw [himg]
  refine lt_of_le_of_lt (lintegral_union_le _ _ _) ?_
  rw [setLIntegral_measure_zero _ _ hnullimg, add_zero,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hsrcM.diff hNmeas)
      (fun w hw => (hfd w hw.1).mono Set.diff_subset) hInj
      (fun A => ENNReal.ofReal (frobSq (prod M A) ^ (-c')))]
  -- flat model + constant
  set C : ℝ := hiJ * loP ^ (-c') with hCdef
  set F : (Fin (flatDim M) → ℝ) → ℝ := fun x =>
    (∏ k, |x (l.divCoord k)| ^ ((l.divExp k : ℝ) - 1 - 2 * c'))
      * (if l.resRank = 0 then (1 : ℝ) else ∑ i, (x (l.resCoord i)) ^ 2) ^ (-c') with hFdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]; exact mul_nonneg hhiJ (Real.rpow_nonneg hloP.le _)
  -- the pointwise integrand bound (real)
  have hdivpos : ∀ k, 1 ≤ l.divExp k := fun k => Nat.one_le_iff_ne_zero.mpr (fun h => by
    have h2 := hdivExp k; rw [h] at h2; norm_num at h2; linarith)
  have hpt : ∀ w ∈ l.srcBox,
      |(Dcomp w).det| * frobSq (prod M (l.chartMap w)) ^ (-c') ≤ C * F (paramsEquivFlat M w) := by
    intro w hw
    set x := paramsEquivFlat M w with hxdef
    have hpw := hpull w hw
    set base : ℝ := residualBaseForm l w with hbasedef
    have hbaseNN : 0 ≤ base := by
      rw [hbasedef]; unfold residualBaseForm; split_ifs with h <;> positivity
    have hFval : F x = (∏ k, |x (l.divCoord k)| ^ ((l.divExp k : ℝ) - 1 - 2 * c')) * base ^ (-c') :=
      rfl
    have hfrobeq : frobSq (prod M (l.chartMap w)) = (∏ k, (x (l.divCoord k)) ^ 2) * rcore w := hpw.1
    have hsqueeze : loP * base ≤ rcore w := hpw.2.1
    have hdet : |(Dcomp w).det| = |(Dψ (β w)).det| * |(Dβ w).det| := abs_det_comp _ _
    have hdetβ : |(Dβ w).det| = ∏ k, |x (l.divCoord k)| ^ (l.divExp k - 1) := (hβ w hw).2
    have hDψle : |(Dψ (β w)).det| ≤ hiJ := (hψ (β w) ⟨w, hw, rfl⟩).2.2.2.2
    have hPnn : (0 : ℝ) ≤ ∏ k, (x (l.divCoord k)) ^ 2 := Finset.prod_nonneg (fun k _ => sq_nonneg _)
    rcases eq_or_lt_of_le (frobSq_nonneg (prod M (l.chartMap w))) with hf0 | hfpos
    · rw [← hf0, Real.zero_rpow (neg_ne_zero.mpr hc'.ne'), mul_zero]
      exact mul_nonneg hCnn (by rw [hFval]; positivity)
    · -- frobSq > 0 ⟹ all factors positive
      obtain ⟨hPpos, hrcpos⟩ : 0 < ∏ k, (x (l.divCoord k)) ^ 2 ∧ 0 < rcore w := by
        rcases mul_pos_iff.mp (by rw [← hfrobeq]; exact hfpos) with h | h
        · exact h
        · exact absurd h.1 (not_lt.mpr hPnn)
      have hbasepos : 0 < base := by
        rcases hbaseNN.lt_or_eq with h | h
        · exact h
        · exfalso; have h2 := hpw.2.2; rw [← h, mul_zero] at h2; linarith
      have hukne : ∀ k, x (l.divCoord k) ≠ 0 := fun k hk =>
        hPpos.ne' (Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; ring))
      -- (∏ uₖ²)^{-c'} = ∏ |uₖ|^{-2c'}
      have hprodrpow : (∏ k, (x (l.divCoord k)) ^ 2) ^ (-c') = ∏ k, |x (l.divCoord k)| ^ (-2 * c') := by
        rw [← Real.finset_prod_rpow _ _ (fun k _ => sq_nonneg _)]
        exact Finset.prod_congr rfl (fun k _ => by
          rw [← sq_abs (x (l.divCoord k)), ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
          congr 1; ring)
      -- ∏ |uₖ|^{divExp-1} · ∏ |uₖ|^{-2c'} = ∏ |uₖ|^{(divExp:ℝ)-1-2c'}
      have hcombine : (∏ k, |x (l.divCoord k)| ^ (l.divExp k - 1))
          * (∏ k, |x (l.divCoord k)| ^ (-2 * c'))
          = ∏ k, |x (l.divCoord k)| ^ ((l.divExp k : ℝ) - 1 - 2 * c') := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun k _ => by
          rw [← Real.rpow_natCast (|x (l.divCoord k)|) (l.divExp k - 1),
            ← Real.rpow_add (abs_pos.mpr (hukne k)), Nat.cast_sub (hdivpos k)]
          congr 1; push_cast; ring)
      rw [hFval, hfrobeq, hdet, hdetβ,
        Real.mul_rpow hPnn hrcpos.le, hprodrpow]
      calc |(Dψ (β w)).det| * (∏ k, |x (l.divCoord k)| ^ (l.divExp k - 1))
              * ((∏ k, |x (l.divCoord k)| ^ (-2 * c')) * rcore w ^ (-c'))
          ≤ hiJ * (∏ k, |x (l.divCoord k)| ^ (l.divExp k - 1))
              * ((∏ k, |x (l.divCoord k)| ^ (-2 * c')) * (loP * base) ^ (-c')) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hDψle
                (Finset.prod_nonneg (fun k _ => pow_nonneg (abs_nonneg _) _)))
              (mul_le_mul_of_nonneg_left (rpow_neg_antitone (mul_pos hloP hbasepos) hsqueeze hc')
                (Finset.prod_nonneg (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)))
              (mul_nonneg (Finset.prod_nonneg (fun k _ => Real.rpow_nonneg (abs_nonneg _) _))
                (Real.rpow_nonneg hrcpos.le _))
              (mul_nonneg hhiJ (Finset.prod_nonneg (fun k _ => pow_nonneg (abs_nonneg _) _)))
        _ = hiJ * loP ^ (-c') * (∏ k, |x (l.divCoord k)| ^ ((l.divExp k : ℝ) - 1 - 2 * c'))
              * base ^ (-c') := by
            rw [Real.mul_rpow hloP.le hbaseNN, ← hcombine]; ring
        _ = C * F x := by rw [hCdef, hFval]; ring
  -- dominate, enlarge to the flat cube, transport, and close with `flat_leaf_model_lt_top`
  have hbound : ∫⁻ w in l.srcBox \ Nbar,
        ENNReal.ofReal |(Dcomp w).det| * ENNReal.ofReal (frobSq (prod M (l.chartMap w)) ^ (-c'))
      ≤ ∫⁻ w in l.srcBox \ Nbar, ENNReal.ofReal (C * F (paramsEquivFlat M w)) :=
    lintegral_mono_ae ((ae_restrict_iff' (hsrcM.diff hNmeas)).mpr (ae_of_all _ (fun w hw => by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hpt w hw.1))))
  refine lt_of_le_of_lt hbound ?_
  -- ∫_{srcBox∖N̄} ofReal (C·F∘pf) ≤ ∫_{pf⁻¹cube} ≤ ∫_{cube} = ofReal C · ∫ ofReal F < ⊤
  have hsub : l.srcBox \ Nbar ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R :=
    Set.diff_subset.trans hRsub
  have hFmeas : Measurable (fun x : Fin (flatDim M) → ℝ => ENNReal.ofReal (F x)) := by
    simp only [hFdef]
    by_cases hr : l.resRank = 0
    · simp only [hr, reduceIte]; fun_prop
    · simp only [if_neg hr]; fun_prop
  have htrans : ∫⁻ w in ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R,
        ENNReal.ofReal (C * F (paramsEquivFlat M w))
      = ∫⁻ x in cubeBox (flatDim M) R, ENNReal.ofReal (C * F x) :=
    (measurePreserving_paramsEquivFlat M).setLIntegral_comp_preimage_emb
      (paramsEquivFlat M).measurableEmbedding (fun x => ENNReal.ofReal (C * F x)) _
  calc ∫⁻ w in l.srcBox \ Nbar, ENNReal.ofReal (C * F (paramsEquivFlat M w))
      ≤ ∫⁻ w in ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R,
          ENNReal.ofReal (C * F (paramsEquivFlat M w)) := lintegral_mono_set hsub
    _ = ∫⁻ x in cubeBox (flatDim M) R, ENNReal.ofReal (C * F x) := htrans
    _ = ENNReal.ofReal C * ∫⁻ x in cubeBox (flatDim M) R, ENNReal.ofReal (F x) := by
        rw [setLIntegral_congr_fun
          (by rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
          (fun x _ => ENNReal.ofReal_mul hCnn), lintegral_const_mul _ hFmeas]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (flat_leaf_model_lt_top R hR l.divCoord l.resCoord hdcInj hrcInj hdisj
          (fun k => (l.divExp k : ℝ) - 1 - 2 * c') (fun k => by have := hdivExp k; linarith)
          c' hc' (fun h => hres h))

end Engine

end DLNFibre.DLN.RLCT
