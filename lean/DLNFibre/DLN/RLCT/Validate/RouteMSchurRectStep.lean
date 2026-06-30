import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCarve
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectChart

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectStep` — the RECTANGULAR per-chart + cap-A interior cover

The item-4 cap-A side: the per-chart integrand factorization (`chart_integrand_factorRect`), the cap-A
per-chart finiteness (`schur_matBoxRect_chart_capA_lt_top` = radial a-axis divisor × the carve
`schurRatioResidRect`), and the cap-A interior cover (`schurCoreRect_capA_interior` = sum over the `mn`
charts). The asymmetric `schur_matBoxGenP_chart_capA_lt_top` / `schurCoreP_capA_interior`.

The cap-B (`t = 0`) directMorse branch + the `min(m,n)` dispatch + the corank-1 leaf + the stub
assembly are the remaining item-4 pieces (the dispatch lives in the consumer once cap-B lands).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- `pivotBlowupOn pivot y ∈ flatBoxRect m n T ↔ |y pivot| ≤ T` on the chart domain (rectangular
`flatBoxG_blowup_mem_iff`; `{N}`-index generic over the flat carrier). -/
theorem flatBoxRect_blowup_mem_iff (m n : ℕ) (T : ℝ) (pivot : Fin (m * n)) (y : Fin (m * n) → ℝ)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (m * n))) pivot) :
    pivotBlowupOn (Finset.univ : Finset (Fin (m * n))) pivot y ∈ flatBoxRect m n T ↔ |y pivot| ≤ T := by
  unfold flatBoxRect chartDomOn at *
  simp only [Set.mem_setOf_eq] at *
  constructor
  · intro h
    have hpp := h pivot
    rw [pivotBlowupOn] at hpp
    simp only [if_pos rfl, Set.mem_Icc] at hpp
    rw [abs_le]; exact hpp
  · intro hp i
    rw [pivotBlowupOn]
    by_cases hi : i = pivot
    · subst hi; simp only [if_pos rfl, Set.mem_Icc]; rw [abs_le] at hp; exact hp
    · simp only [if_neg hi, Finset.mem_univ, if_true, Set.mem_Icc]
      have hyi : |y i| ≤ 1 := hy i (Finset.mem_univ i) hi
      have hb : |y pivot * y i| ≤ |y pivot| := by
        rw [abs_mul]; nlinarith [abs_nonneg (y pivot), abs_nonneg (y i), abs_nonneg (y pivot * y i)]
      have hbb : |y pivot * y i| ≤ T := le_trans hb hp
      rw [abs_le] at hbb; exact hbb

/-- **The rectangular per-chart factor.** On the chart, the flattened radial Jacobian × `gFlatRect`
indicator factors as the radial `a`-axis indicator `|y pivot|^{(mn−1)−2c'}` × the angular residual
`innerSRect`. The asymmetric `chart_integrand_factorGen`. -/
theorem chart_integrand_factorRect (m n p : ℕ) (c' : ℝ) (hc0 : 0 < c') (T : ℝ) (hT : 0 < T)
    (pivot : Fin (m * n)) (y : Fin (m * n) → ℝ) (hyp0 : y pivot ≠ 0)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (m * n))) pivot) :
    ENNReal.ofReal (|y pivot| ^ (m * n - 1))
        * (flatBoxRect m n T).indicator (gFlatRect m n p c' T) (pivotBlowupOn
            (Finset.univ : Finset (Fin (m * n))) pivot y)
      = (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) (y pivot)
        * innerSRect m n p c' T pivot y := by
  by_cases hmem : pivotBlowupOn (Finset.univ : Finset (Fin (m * n))) pivot y ∈ flatBoxRect m n T
  · have hyp : |y pivot| ≤ T := (flatBoxRect_blowup_mem_iff m n T pivot y hy).1 hmem
    rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (s := Set.Icc (-T) T) (by rw [Set.mem_Icc, ← abs_le]; exact hyp)]
    rw [gFlatRect_blowup_radial m n p c' T pivot y, innerSRect]
    have hpull : ∀ S : Fin n → Fin p → ℝ,
        ENNReal.ofReal (((y pivot) ^ 2 * frobSq (rmatMul (RmatRect m n pivot y) S)) ^ (-c'))
          = ENNReal.ofReal ((((y pivot) ^ 2) ^ (-c')))
            * ENNReal.ofReal ((frobSq (rmatMul (RmatRect m n pivot y) S)) ^ (-c')) := by
      intro S
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ← Real.mul_rpow (by positivity) (frobSq_nonneg _)]
    rw [lintegral_congr hpull, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hb : ((y pivot) ^ 2 : ℝ) = |y pivot| ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hpos : (0 : ℝ) < |y pivot| := abs_pos.2 hyp0
    rw [hb, ← Real.rpow_natCast (|y pivot|) (m * n - 1), ← Real.rpow_mul (le_of_lt hpos),
      ← Real.rpow_add hpos]
    congr 1; push_cast; ring
  · have hyp : ¬ |y pivot| ≤ T := fun h => hmem ((flatBoxRect_blowup_mem_iff m n T pivot y hy).2 h)
    rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (s := Set.Icc (-T) T)
        (by rw [Set.mem_Icc, ← abs_le]; exact hyp), zero_mul, mul_zero]

/-- The radial cap `rectSchurLambda p m n ≤ mn/2` (the `t=0` stratum `(m)(n)+0 = mn` caps the inf'). -/
theorem rectSchurLambda_le_mul (m n p : ℕ) : rectSchurLambda p m n ≤ ((m : ℝ) * (n : ℝ)) / 2 := by
  rw [rectSchurLambda]
  have h := minAdm_mnp_le_mul m n p
  have : ((minAdm (![m, n, p] : Fin 3 → ℕ) : ℝ)) ≤ (m : ℝ) * (n : ℝ) := by
    rw [show (m : ℝ) * (n : ℝ) = ((m * n : ℕ) : ℝ) by push_cast; ring]
    exact_mod_cast h
  linarith

/-- **The cap-A per-chart finiteness.** The rectangular per-chart integral is finite for
`0 < c' < rectSchurLambda p m n` (`min(m,n) ≥ 2`, interior stratum `rectSchurLambda > p/2`): the radial
a-axis divisor `|a|^{mn−1−2c'}` (finite ⟺ `c' < mn/2`) × the angular residual `schurRatioResidRect`,
Tonelli-separated via `piRatioRect`. The asymmetric `schur_matBoxGenP_chart_capA_lt_top`. -/
theorem schur_matBoxRect_chart_capA_lt_top (m n p : ℕ) (hmm : 2 ≤ m) (hnn : 2 ≤ n) (hp : 0 < p)
    (hIH : RectSchurLowerIH p (rectSchurLambda p) m n)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < rectSchurLambda p m n)
    (hmid : (p : ℝ) / 2 < rectSchurLambda p m n) (pivot : Fin (m * n)) (T : ℝ) (hT : 0 < T) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (m * n))) pivot \ pivotZeroOn pivot,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (m * n))) pivot y).det|
          * (flatBoxRect m n T).indicator (gFlatRect m n p c' T) (pivotBlowupOn
              (Finset.univ : Finset (Fin (m * n))) pivot y)
      < ⊤ := by
  have hmn : 0 < m * n := by positivity
  obtain ⟨N, hN⟩ : ∃ N, m * n = N + 1 := ⟨m * n - 1, by omega⟩
  have hcr0 : c' < ((m : ℝ) * (n : ℝ)) / 2 := lt_of_lt_of_le hc' (rectSchurLambda_le_mul m n p)
  have hcr : c' < (((m * n : ℕ)) : ℝ) / 2 := by rw [Nat.cast_mul]; exact hcr0
  have hdet : ∀ y : Fin (m * n) → ℝ,
      |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (m * n))) pivot y).det|
        = |y pivot| ^ (m * n - 1) := fun y => pivotBlowupOnDeriv_det_rect m n pivot y
  simp only [hdet]
  have hmsD : MeasurableSet
      (chartDomOn (Finset.univ : Finset (Fin (m * n))) pivot \ pivotZeroOn pivot) := by
    refine MeasurableSet.diff ?_ ?_
    · have heq : chartDomOn (Finset.univ : Finset (Fin (m * n))) pivot
          = ⋂ k ∈ (Finset.univ.erase pivot), {y : Fin (m * n) → ℝ | |y k| ≤ 1} := by
        ext y
        simp only [chartDomOn, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_erase,
          Finset.mem_univ, and_true, true_implies]
      rw [heq]
      refine Finset.measurableSet_biInter (Finset.univ.erase pivot) (fun k _ => ?_)
      exact measurableSet_le ((measurable_pi_apply k).abs) measurable_const
    · exact (measurable_pi_apply pivot (measurableSet_singleton 0))
  rw [setLIntegral_congr_fun hmsD
    (fun y hy => chart_integrand_factorRect m n p c' hc0 T hT pivot y hy.2 hy.1)]
  set e := piRatioRect m n N hN pivot with he
  have hmp : MeasurePreserving e (volume) (volume) := measurePreserving_piRatioRect m n N hN pivot
  have hpre : (chartDomOn (Finset.univ : Finset (Fin (m * n))) pivot \ pivotZeroOn pivot)
      = e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))) := by
    ext y
    simp only [chartDomOn, pivotZeroOn, Set.mem_diff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, he]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [piRatioRect_apply_fst]; exact h2, fun j => ?_⟩
      rw [Set.mem_Icc, ← abs_le, piRatioRect_apply_snd]
      exact h1 _ (Finset.mem_univ _) (piRatioRect_ratioIdx_ne m n N hN pivot j)
    · rintro ⟨h1, h2⟩
      rw [piRatioRect_apply_fst] at h1
      refine ⟨fun k _ hk => ?_, h1⟩
      have hne : finCongr hN k ≠ finCongr hN pivot := fun h => hk ((finCongr hN).injective h)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
      have hk_eq : k = (finCongr hN).symm ((finCongr hN pivot).succAbove j) := by
        rw [hj]; exact ((finCongr hN).symm_apply_apply k).symm
      have hj2 := h2 j
      rw [Set.mem_Icc, ← abs_le, piRatioRect_apply_snd m n N hN pivot y j] at hj2
      rw [hk_eq]; exact hj2
  set g : (Fin (m * n) → ℝ) → ℝ≥0∞ := fun y =>
    (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) (y pivot)
      * innerSRect m n p c' T pivot y with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    refine Measurable.mul ?_ (measurable_innerSRect m n p c' T pivot)
    have hind : Measurable (fun a : ℝ =>
        (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) a) := by
      refine Measurable.indicator ?_ measurableSet_Icc
      exact ENNReal.measurable_ofReal.comp ((measurable_id.abs).pow_const _)
    exact hind.comp (measurable_pi_apply pivot)
  rw [hpre]
  have hSms : MeasurableSet
      (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))) :=
    MeasurableSet.prod (by measurability) (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  have key := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun q => g (e.symm q))
    (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)))
  have htrans : (∫⁻ y in e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ
        (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))), g y)
      = ∫⁻ q in (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))),
          g (e.symm q) := by
    rw [← key]
    refine setLIntegral_congr_fun (e.measurable hSms) (fun y _ => ?_)
    rw [MeasurableEquiv.symm_apply_apply]
  rw [htrans]
  have hgsymm_meas : Measurable (fun q : ℝ × (Fin N → ℝ) => g (e.symm q)) :=
    hgmeas.comp e.symm.measurable
  rw [Measure.volume_eq_prod ℝ (Fin N → ℝ), setLIntegral_prod _ hgsymm_meas.aemeasurable]
  have hfactor : ∀ a : ℝ, ∀ z : Fin N → ℝ,
      g (e.symm (a, z))
        = (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) a
          * innerSRect m n p c' T pivot (e.symm (0, z)) := by
    intro a z
    have hp_eq : (e.symm (a, z)) pivot = a := by rw [he]; exact piRatioRect_symm_pivot m n N hN pivot a z
    have hoff : innerSRect m n p c' T pivot (e.symm (a, z))
        = innerSRect m n p c' T pivot (e.symm (0, z)) := by
      refine innerSRect_offpivot m n p c' T pivot _ _ (fun i hi => ?_)
      rw [he]; exact piRatioRect_symm_offpivot m n N hN pivot a 0 z i hi
    show (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) ((e.symm (a, z)) pivot)
        * innerSRect m n p c' T pivot (e.symm (a, z)) = _
    rw [hp_eq, hoff]
  have hradfin : (∫⁻ a in {a : ℝ | a ≠ 0},
        (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) a) < ⊤ := by
    have hle1 : (∫⁻ a in {a : ℝ | a ≠ 0},
          (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) a)
        ≤ ∫⁻ a, (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) a := by
      have := lintegral_mono_set (μ := volume) (s := {a : ℝ | a ≠ 0}) (t := Set.univ)
        (Set.subset_univ _)
        (f := (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))))
      rwa [setLIntegral_univ] at this
    have heq2 : (∫⁻ a, (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) a)
        = ∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c')) :=
      lintegral_indicator measurableSet_Icc _
    rw [heq2] at hle1
    have hexp : (((m * n - 1 : ℕ) : ℝ) - 2 * c') = (((m * n : ℕ) : ℝ) - 1 - 2 * c') := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hdiv := radial_aAxis_divisor_rect m n (by omega) T hT c' hcr
    rw [← hexp] at hdiv
    exact lt_of_le_of_lt hle1 hdiv
  have hratiofin : (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSRect m n p c' T pivot (e.symm (0, z))) < ⊤ :=
    schurRatioResidRect m n N p hN hmm hnn hp hIH c' hc0 hc' hmid pivot T hT
  have hinner : ∀ a : ℝ,
      (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)), g (e.symm (a, z)))
        = (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) a
          * ∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
              innerSRect m n p c' T pivot (e.symm (0, z)) := by
    intro a
    have hradne : (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((m * n - 1 : ℕ) : ℝ) - 2 * c'))) a ≠ ⊤ := by
      rw [Set.indicator_apply]; split <;> simp [ENNReal.ofReal_ne_top]
    rw [lintegral_congr (fun z => hfactor a z), lintegral_const_mul' _ _ hradne]
  rw [lintegral_congr hinner, lintegral_mul_const' _ _ hratiofin.ne]
  exact ENNReal.mul_lt_top hradfin hratiofin

/-- **The cap-A interior cover.** `RectSchurCore m n p c' T` for `0 < c' < rectSchurLambda p m n`
(`min(m,n) ≥ 2`, interior stratum): the `mn`-chart radial-Δ cover (`matBoxRect_outer_flat` +
`gFlatRect_cover_sum`) reduces to a sum over `mn` charts, each finite by the cap-A per-chart
`schur_matBoxRect_chart_capA_lt_top`. The asymmetric `schurCoreP_capA_interior`. -/
theorem schurCoreRect_capA_interior (m n p : ℕ) (hmm : 2 ≤ m) (hnn : 2 ≤ n) (hp : 0 < p)
    (hIH : RectSchurLowerIH p (rectSchurLambda p) m n)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < rectSchurLambda p m n)
    (hmid : (p : ℝ) / 2 < rectSchurLambda p m n) (T : ℝ) (hT : 0 < T) :
    RectSchurCore m n p c' T := by
  rw [RectSchurCore, matBoxRect_outer_flat m n p c' T, gFlatRect_cover_sum m n p (by positivity) c' T]
  exact ENNReal.sum_lt_top.2
    (fun q _ => schur_matBoxRect_chart_capA_lt_top m n p hmm hnn hp hIH c' hc0 hc' hmid q T hT)

end DLNFibre.DLN.RLCT
