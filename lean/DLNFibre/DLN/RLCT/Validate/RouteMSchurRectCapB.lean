import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectStep

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCapB` — the RECTANGULAR cap-B directMorse branch (item 4)

The `t = 0` binding-stratum branch of the rectangular per-step (`min(m,n) ≥ 2`, `rectSchurLambda p m n ≤
p/2`): the angular residual KEEPS the Schur residual (no recursion), closed by the abstract-`Z` Morse
dominator at `c' < p/2`. The asymmetric (`Δ : Fin m → Fin n`) generalisation of `RouteMSchurDirectMorseP`'s
`frobSq_capB_inner_le` / `schurRatioResidP_capB_lt_top` / `schur_matBoxGenP_chart_lt_top` /
`schurCoreP_directMorse`, built on the rectangular interface (`RmatRectNorm`, `innerSRect_eq_norm`,
`schur_minorPivot_split_rect`, `frobSqTopRowRect_eq_shear`, `stepShearRect`) + the radial half from
`RouteMSchurRectStep` (`chart_integrand_factorRect`, `flatBoxRect_blowup_mem_iff`).

The residual is `(m−1)×(n−1)` (NOT square `(r−1)×(r−1)`); the Morse-dominator `Z`-box is `(n−1)×p` (the
contracted dim `n`); the per-`R` bound is `R`-uniform (so the per-`z` integration over the ratio box
factors out the constant).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The rectangular cap-B inner-`S` bound (per angular matrix `R`) -/

/-- **The rectangular cap-B inner-`S` bound by a `z`-UNIFORM constant.** For an `m×n` matrix `R`
(`1 ≤ m, 1 ≤ n`) with pivot `R ⟨0⟩ ⟨0⟩ = 1` and `|entries| ≤ 1`, and `c' < p/2`, the inner-`S` integral
`∫_{S∈matBox n p T} frobSq(R·S)^{−c'}` is bounded by `ofReal(c₀^{−c'}) · Kbound p c' (n·T) ·
vol(matBox (n−1) p (n·T))` — INDEPENDENT of `R` (hence of the chart `z`). N2b (`t = 1`) lower-bounds
`frobSq(R·S)` by `c₀·(frobSq row0 + frobSq(Sc·S_bot))` (`ofReal_rpow_le_const_mul`, zero-guard from the
upper bound); the top-row bridge (`frobSqTopRowRect_eq_shear`) + `stepShearRect` peel the `Fin p` Morse
block (box enlarged to `n·T`); the abstract-`Z` Morse dominator's `Kbound` is `W`-INDEPENDENT
(`radial_morse_dominates_absZ_le`). Cap-B KEEPS the residual (binding stratum `t = 0`); no recursion. The
asymmetric `frobSq_capB_inner_le`. -/
theorem frobSq_capB_inner_rect_le (m n p : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (R : Fin m → Fin n → ℝ)
    (hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) (hbd : ∀ a b, |R a b| ≤ 1)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < (p : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ S in matBox n p T, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')))
      ≤ ENNReal.ofReal ((schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 hm hn).choose ^ (-c'))
        * (Kbound p c' ((n : ℕ) * T) * volume (matBox (n - 1) p ((n : ℕ) * T))) := by
  classical
  set RM : Matrix (Fin m) (Fin n) ℝ := Matrix.of R with hRM
  set c₀ := (schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 hm hn).choose with hc₀def
  obtain ⟨c₁, hc₀, hc₁, hN2b⟩ := (schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 hm hn).choose_spec
  -- the 1×1 pivot minor M11 = [1]: det = 1, dominance from |entries| ≤ 1, det ≠ 0
  set M11 : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.of (fun a b : Fin 1 => RM ⟨a, lt_of_lt_of_le a.2 hm⟩ ⟨b, lt_of_lt_of_le b.2 hn⟩) with hM11
  have hM11_one : M11 = 1 := by
    ext a b; fin_cases a; fin_cases b
    simp only [hM11, hRM, Matrix.of_apply, Matrix.one_apply_eq]; exact hpiv
  have hpivdet : M11.det = 1 := by rw [hM11_one]; simp
  have hpivot : ∀ (I : Fin 1 → Fin m) (J : Fin 1 → Fin n), |(RM.submatrix I J).det| ≤ |M11.det| := by
    intro I J
    rw [Matrix.det_fin_one, hpivdet, abs_one, Matrix.submatrix_apply]
    exact hbd (I 0) (J 0)
  have hne : M11.det ≠ 0 := by rw [hpivdet]; norm_num
  obtain ⟨Sc, hSceq, _, _⟩ := hN2b RM (fun _ _ => 0) hbd hpivot hne
  set X : (Fin n → Fin p → ℝ) → ℝ := fun S =>
    frobSq (fun a : Fin 1 => rmatMul (fun x y => RM x y) S ⟨a, lt_of_lt_of_le a.2 hm⟩)
      + frobSq (rmatMul (fun a b => Sc a b) (fun a : Fin (n - 1) => S ⟨1 + a, by omega⟩)) with hXdef
  have hXnn : ∀ S, 0 ≤ X S := fun S => add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)
  have hlow : ∀ S, c₀ * X S ≤ frobSq (rmatMul RM S) := by
    intro S
    obtain ⟨Sc', hSceq', hlo, _⟩ := hN2b RM S hbd hpivot hne
    have : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst this; simpa only [hXdef] using hlo
  have hupp : ∀ S, frobSq (rmatMul RM S) ≤ c₁ * X S := by
    intro S
    obtain ⟨Sc', hSceq', _, hup⟩ := hN2b RM S hbd hpivot hne
    have : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst this; simpa only [hXdef] using hup
  have hpt : ∀ S, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c'))
      ≤ ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) := by
    intro S
    refine ofReal_rpow_le_const_mul (X S) (frobSq (rmatMul R S)) c₀ c'
      hc0 hc₀ (hXnn S) (frobSq_nonneg _) (hlow S) ?_
    intro hX0
    have := hupp S; rw [hX0, mul_zero] at this
    exact le_antisymm this (frobSq_nonneg _)
  set bcoup : Fin (n - 1) → ℝ := fun a => RM ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩ with hbcoup
  have hbcoup_le : ∀ a, |bcoup a| ≤ 1 := fun a => hbd _ _
  have hpiv' : (fun x y => RM x y) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := hpiv
  have hXrw : ∀ S, X S
      = (∑ q, (S ⟨0, by omega⟩ q + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
        + frobSq (rmatMul (fun a b => Sc a b) (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q)) := by
    intro S
    simp only [hXdef]
    rw [frobSqTopRowRect_eq_shear m n p hm hn (fun x y => RM x y) hpiv' S]
  obtain ⟨pm, hpm⟩ : ∃ pm, p = pm + 1 := by
    refine ⟨p - 1, ?_⟩
    have : 0 < p := by
      by_contra h
      push_neg at h; interval_cases p; simp at hc'; linarith
    omega
  calc (∫⁻ S in matBox n p T, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')))
      ≤ ∫⁻ S in matBox n p T, ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (c₀ ^ (-c')) * ∫⁻ S in matBox n p T, ENNReal.ofReal ((X S) ^ (-c')) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (c₀ ^ (-c'))
          * ∫⁻ S in matBox n p T,
              ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q
                  + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
                + frobSq (rmatMul (fun a b => Sc a b)
                    (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')) := by
        congr 1; exact lintegral_congr (fun S => by rw [hXrw S])
    _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (∫⁻ S_bot in matBox (n - 1) p T, ∫⁻ T' in morseBox p ((n : ℕ) * T),
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => Sc a b) S_bot)) ^ (-c'))) :=
        mul_le_mul_left' (stepShearRect m n p hn bcoup hbcoup_le (Matrix.of (fun a b => Sc a b)) T hT c') _
    _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (Kbound p c' ((n : ℕ) * T) * volume (matBox (n - 1) p ((n : ℕ) * T))) := by
        refine mul_le_mul_left' ?_ _
        -- enlarge the S_bot box (radius T ⊆ n·T), then the abstract-Z Morse dominator's _le bound
        have hcap : c' < ((pm + 1 : ℝ)) / 2 := by rw [hpm] at hc'; push_cast at hc'; exact hc'
        have hsub : matBox (n - 1) p T ⊆ matBox (n - 1) p ((n : ℕ) * T) := by
          intro Y hY i k; have := Set.mem_Icc.1 (hY i k); rw [Set.mem_Icc]
          have hTnT : T ≤ (n : ℕ) * T := le_mul_of_one_le_left hT.le
            (by exact_mod_cast (show (1:ℕ) ≤ n by omega))
          constructor <;> [linarith [this.1]; linarith [this.2]]
        refine le_trans (lintegral_mono_set hsub) ?_
        have hle := radial_morse_dominates_absZ_le (m := pm) (Ω := Fin (n - 1) → Fin p → ℝ)
          (volume) c' hcap hc0.le ((n : ℕ) * T) (by positivity)
          (fun S_bot => frobSq (rmatMul (fun a b => Sc a b) S_bot))
          (fun _ => frobSq_nonneg _) (matBox (n - 1) p ((n : ℕ) * T))
        have hpconv : pm + 1 = p := hpm.symm
        subst hpconv
        exact hle

/-! ## The rectangular cap-B per-chart angular residual -/

/-- **The rectangular cap-B angular residual finiteness (per chart).** For `c' < p/2`, the angular
box-integral of the inner-`S` integrand over the `mn−1` ratio box is finite. Per `z`, the angular matrix
`R := RmatRectNorm (piRatioRect.symm (0,z))` has pivot `1` (`RmatRectNorm_pivot`) and `|entries| ≤ 1`
(`RmatRectNorm_offpivot_le`), so `frobSq_capB_inner_rect_le` gives a `z`-uniform bound (the abstract-`Z`
Morse dominator's `Kbound` is `W`-independent, `c₀` chosen before `R`); the integral over the finite-volume
ratio box is finite. The asymmetric `schurRatioResidP_capB_lt_top` (NO recursion). -/
theorem schurRatioResidRect_capB_lt_top (m n N p : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < (p : ℝ) / 2) (pivot : Fin (m * n)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSRect m n p c' T pivot ((piRatioRect m n N hN pivot).symm (0, z)))
      < ⊤ := by
  classical
  set C : ℝ≥0∞ :=
    ENNReal.ofReal ((schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 hm hn).choose ^ (-c'))
      * (Kbound p c' ((n : ℕ) * T) * volume (matBox (n - 1) p ((n : ℕ) * T))) with hC
  have hpt : ∀ z ∈ Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1),
      innerSRect m n p c' T pivot ((piRatioRect m n N hN pivot).symm (0, z)) ≤ C := by
    intro z hz
    rw [innerSRect_eq_norm m n N p hN hm hn c' T pivot z]
    have hpiv : RmatRectNorm m n N hN hm hn pivot z ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 :=
      RmatRectNorm_pivot m n N hN hm hn pivot z
    have hbd : ∀ a b, |RmatRectNorm m n N hN hm hn pivot z a b| ≤ 1 := by
      intro a b
      by_cases hab : a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩
      · rw [hab.1, hab.2, hpiv]; norm_num
      · exact RmatRectNorm_offpivot_le m n N hN hm hn pivot z hz a b hab
    exact frobSq_capB_inner_rect_le m n p hm hn (RmatRectNorm m n N hN hm hn pivot z) hpiv hbd
      c' hc0 hc' T hT
  have hbox : (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSRect m n p c' T pivot ((piRatioRect m n N hN pivot).symm (0, z)))
      ≤ ∫⁻ _z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)), C :=
    setLIntegral_mono_ae' (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (ae_of_all _ (fun z hz => hpt z hz))
  refine lt_of_le_of_lt hbox ?_
  rw [setLIntegral_const]
  refine ENNReal.mul_lt_top ?_ ?_
  · refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    obtain ⟨pm, hpm⟩ : ∃ pm, p = pm + 1 := by
      refine ⟨p - 1, ?_⟩
      have : 0 < p := by by_contra h; push_neg at h; interval_cases p; simp at hc'; linarith
      omega
    have hcap : c' < ((pm + 1 : ℝ)) / 2 := by rw [hpm] at hc'; push_cast at hc'; exact hc'
    have hKfin := Kbound_lt_top pm ((n : ℕ) * T) (by positivity) c' hcap
    refine ENNReal.mul_lt_top ?_ (matBox_volume_lt_top (n - 1) p ((n : ℕ) * T))
    rw [hpm]; exact hKfin
  · exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

/-! ## The rectangular cap-B per-chart + the directMorse cover -/

/-- **The rectangular cap-B per-chart finiteness.** The radial blow-up chart integral (Jacobian
`|y pivot|^{mn−1}`) is finite for `0 < c' < min(p, mn)/2` (`min(m,n) ≥ 1`, the cap-B regime, binding
stratum `t = 0`). The `piRatioRect` MP + Tonelli factor the pivot axis (`radial_aAxis_divisor_rect`,
`c' < mn/2`) from the `mn−1` ratios; the ratio residual is the cap-B `schurRatioResidRect_capB_lt_top`
(`c' < p/2`, NO recursion). The asymmetric `schur_matBoxGenP_chart_lt_top`. -/
theorem schur_matBoxRect_chart_capB_lt_top (m n p : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (c' : ℝ) (hc0 : 0 < c') (hcp : c' < (p : ℝ) / 2) (hcr : c' < ((m * n : ℕ) : ℝ) / 2)
    (pivot : Fin (m * n)) (T : ℝ) (hT : 0 < T) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (m * n))) pivot \ pivotZeroOn pivot,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (m * n))) pivot y).det|
          * (flatBoxRect m n T).indicator (gFlatRect m n p c' T) (pivotBlowupOn
              (Finset.univ : Finset (Fin (m * n))) pivot y)
      < ⊤ := by
  have hmn : 0 < m * n := by positivity
  obtain ⟨N, hN⟩ : ∃ N, m * n = N + 1 := ⟨m * n - 1, by omega⟩
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
    schurRatioResidRect_capB_lt_top m n N p hN hm hn c' hc0 hcp pivot T hT
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

/-- **The rectangular cap-B directMorse finiteness.** `RectSchurCore m n p c' T` for
`0 < c' < min(p, mn)/2` (the cap-B regime, where the binding stratum is `t = 0`, so
`rectSchurLambda p m n ≤ p/2`). The `mn`-chart radial-`Δ` cover (`matBoxRect_outer_flat` +
`gFlatRect_cover_sum`) reduces to a sum over `mn` charts; each chart = the radial axis `|y|^{mn−1−2c'}`
(`radial_aAxis_divisor_rect`, `c' < mn/2`) × the angular residual (`schurRatioResidRect_capB_lt_top`,
`c' < p/2`). NO recursion (unlike the cap-A firing). The asymmetric `schurCoreP_directMorse`. -/
theorem schurCoreRect_directMorse (m n p : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (c' : ℝ) (hc0 : 0 < c')
    (hcp : c' < (p : ℝ) / 2) (hcr : c' < ((m * n : ℕ) : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    RectSchurCore m n p c' T := by
  rw [RectSchurCore, matBoxRect_outer_flat m n p c' T, gFlatRect_cover_sum m n p (by positivity) c' T]
  exact ENNReal.sum_lt_top.2
    (fun q _ => schur_matBoxRect_chart_capB_lt_top m n p hm hn c' hc0 hcp hcr q T hT)

/-! ## The corank-1 leaf (`min(m,n) = 1`) -/

/-- `minAdm(![m,n,p]) ≤ p` when `min(m,n) = 1` (the `t = 1` stratum is `(m−1)(n−1)+p = p`, since one of
`m−1, n−1` is `0`). Hence `rectSchurLambda p m n = ½·minAdm ≤ p/2`. -/
theorem minAdm_mnp_le_p_of_min_one (m n p : ℕ) (hmn1 : min m n = 1) :
    minAdm (![m, n, p] : Fin 3 → ℕ) ≤ p := by
  rw [minAdm_mnp_eq_inf]
  have hmem : (1 : ℕ) ∈ Finset.range (min m n + 1) := by rw [hmn1]; simp
  refine le_trans (Finset.inf'_le _ hmem) ?_
  have hone : (m - 1) * (n - 1) = 0 := by
    rcases Nat.le_total m n with h | h
    · have : m = 1 := by omega
      rw [this]; simp
    · have : n = 1 := by omega
      rw [this]; simp
  rw [hone]; simp

/-- **The rectangular corank-1 leaf.** `RectSchurCore m n p c' T` for `0 < c' < rectSchurLambda p m n`
with `min(m,n) = 1` (one of `m, n` is `1`; the recursion measure bottoms out — the `j = 1` peel would land
on the empty `min(m−1,n−1) = 0` core). Since `rectSchurLambda p m n = ½·minAdm ≤ p/2` here
(`minAdm_mnp_le_p_of_min_one`) AND `≤ mn/2` (`rectSchurLambda_le_mul`), BOTH cap-B caps hold, so the
directMorse cover `schurCoreRect_directMorse` fires (NO recursion). The rectangular analog of the square
`schurCoreP_one` Morse leaf — but here it is the same cap-B machinery, not a separate separable form. -/
theorem schurCoreRect_one (m n p : ℕ) (hmn1 : min m n = 1)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < rectSchurLambda p m n) (T : ℝ) (hT : 0 < T) :
    RectSchurCore m n p c' T := by
  have hm : 1 ≤ m := by omega
  have hn : 1 ≤ n := by omega
  have hcp : c' < (p : ℝ) / 2 := by
    have hle : rectSchurLambda p m n ≤ (p : ℝ) / 2 := by
      rw [rectSchurLambda]
      have h := minAdm_mnp_le_p_of_min_one m n p hmn1
      have : ((minAdm (![m, n, p] : Fin 3 → ℕ) : ℝ)) ≤ (p : ℝ) := by exact_mod_cast h
      linarith
    linarith
  have hcr : c' < ((m * n : ℕ) : ℝ) / 2 := by
    have hle : rectSchurLambda p m n ≤ ((m : ℝ) * (n : ℝ)) / 2 := rectSchurLambda_le_mul m n p
    rw [Nat.cast_mul]; linarith
  exact schurCoreRect_directMorse m n p hm hn c' hc0 hcp hcr T hT

/-! ## The full rectangular per-step dispatch (the stub replacement) -/

/-- `rectSchurLambda p 0 n = 0` and `rectSchurLambda p m 0 = 0` (the `min = 0` corank-0 leaf — one width
`0` collapses `minAdm` to `0`, so the per-step hypothesis `c' < rectSchurLambda` is incompatible with
`0 < c'`). Read off the threshold contract `rectSchurLambda_satisfies_threshold`. -/
theorem rectSchurLambda_eq_zero_of_min_zero (m n p : ℕ) (hmn0 : min m n = 0) :
    rectSchurLambda p m n = 0 := by
  rcases Nat.min_eq_zero_iff.1 hmn0 with hm0 | hn0
  · rw [hm0]; exact (rectSchurLambda_satisfies_threshold p).lambda0_left
  · rw [hn0]; exact (rectSchurLambda_satisfies_threshold p).lambda0_right

/-- **The rectangular per-step `RectSchurRecStep` (the real dispatch — the stub replacement).**
`RectSchurRecStep p (rectSchurLambda p)`: for all `(m,n)`, given the threshold contract and the joint lower
IH, the `(m,n)` core is finite below `rectSchurLambda p m n`. Dispatches on the recursion measure
`min(m,n)`:
* `min(m,n) = 0` — vacuous (`rectSchurLambda = 0`, contradicts `0 < c'`);
* `min(m,n) = 1` — the corank-1 leaf `schurCoreRect_one` (cap-B machinery, no recursion);
* `min(m,n) ≥ 2` — split on `le_or_gt (rectSchurLambda p m n) (p/2)`: cap-B `schurCoreRect_directMorse`
  (binding stratum `t = 0`, no recursion) or the interior carve `schurCoreRect_capA_interior` (the
  recursion-driven `M22 ↦ Sc` carve + the lower IH `hIH`). The asymmetric `schurRecStep_p`. -/
theorem rectSchurRecStep_mnp (p : ℕ) : RectSchurRecStep p (rectSchurLambda p) := by
  intro m n hlam hIH c' hc0 hclt T hT
  -- dispatch on the recursion measure min(m,n)
  rcases Nat.lt_or_ge (min m n) 2 with hlt | hge
  · -- min(m,n) ∈ {0, 1}
    rcases Nat.lt_or_ge (min m n) 1 with hlt0 | hge1
    · -- min = 0: vacuous
      have hmn0 : min m n = 0 := by omega
      exact absurd hclt (by rw [rectSchurLambda_eq_zero_of_min_zero m n p hmn0]; exact not_lt.2 hc0.le)
    · -- min = 1: the corank-1 leaf
      have hmn1 : min m n = 1 := by omega
      exact schurCoreRect_one m n p hmn1 c' hc0 hclt T hT
  · -- min(m,n) ≥ 2: cap-B directMorse (lam ≤ p/2) or interior carve
    have hmm : 2 ≤ m := by omega
    have hnn : 2 ≤ n := by omega
    have hp : 0 < p := by
      rcases Nat.eq_zero_or_pos p with hp0 | hp; swap; · exact hp
      -- p = 0 ⟹ rectSchurLambda 0 m n = 0 (minAdm via t = min(m,n): (m−t)(n−t) ≤ 0 not forced; but
      -- the t = min stratum gives 0 when p = 0 only if a width hits 0 — instead use the radial cap and
      -- the fact that the t = min(m,n) stratum is (m−min)(n−min) which need not be 0. We argue directly:
      -- p = 0 forces minAdm ≤ minAdm_mnp_subadd at j = min, but simplest: c' < lam ≤ mn/2 is fine; the
      -- carve needs 0 < p. With p = 0 the box S : n×0 is a point, frobSq ≡ 0, integrand 0^{−c'}. Rule out
      -- p = 0 by the threshold: rectSchurLambda 0 m n ≤ p/2 = 0 (minAdm_mnp_le via t = min has tp = 0 and
      -- (m−min)(n−min); for the BINDING value we need ≤ 0). Use minAdm ≤ (m−min)(n−min) + min·0.
      exfalso
      have hle : rectSchurLambda p m n ≤ ((m : ℝ) * (n : ℝ)) / 2 := rectSchurLambda_le_mul m n p
      -- with p = 0, the t = min(m,n) stratum value is (m−min)(n−min) which is 0 (one factor vanishes)
      have hzero : minAdm (![m, n, p] : Fin 3 → ℕ) = 0 := by
        rw [minAdm_mnp_eq_inf]
        refine le_antisymm ?_ (Nat.zero_le _)
        have hmem : min m n ∈ Finset.range (min m n + 1) := by simp
        refine le_trans (Finset.inf'_le _ hmem) ?_
        rw [hp0]
        have hfac : (m - min m n) * (n - min m n) = 0 := by
          rcases Nat.le_total m n with h | h
          · rw [Nat.min_eq_left h]; simp
          · rw [Nat.min_eq_right h]; simp
        rw [hfac]; simp
      rw [rectSchurLambda, hzero] at hclt
      simp only [Nat.cast_zero, zero_div] at hclt
      exact absurd hclt (not_lt.2 hc0.le)
    rcases le_or_gt (rectSchurLambda p m n) ((p : ℝ) / 2) with hcap | hcap
    · -- cap-B: lam ≤ p/2, so c' < p/2 and c' < mn/2 (via radial cap)
      have hcp : c' < (p : ℝ) / 2 := lt_of_lt_of_le hclt hcap
      have hcr : c' < ((m * n : ℕ) : ℝ) / 2 := by
        have hle : rectSchurLambda p m n ≤ ((m : ℝ) * (n : ℝ)) / 2 := rectSchurLambda_le_mul m n p
        rw [Nat.cast_mul]; linarith
      exact schurCoreRect_directMorse m n p (by omega) (by omega) c' hc0 hcp hcr T hT
    · -- cap-A interior: lam > p/2, the recursion-driven carve
      exact schurCoreRect_capA_interior m n p hmm hnn hp hIH c' hc0 hclt hcap T hT

/-! ## The general-`(M0,M1,M2)` deliverables (the UPPER leg, now CLOSED via the real dispatch) -/

/-- **The general-`(M0,M1,M2)` `hbox`.** `RouteMBoxThresholdFinite (![m,n,p])` for ALL `m, n, p` — the
asymmetric analog of `routeMBoxThresholdFinite_rrp`. Assembly: the threshold match
(`rectSchurLambda p m n = ½·minAdm`, `rfl`) + the reshape (`routeMLayerBoxIntegral_mnp_eq`) to the
rectangular two-matrix box, finite by `rectCore_schurGen_lt_top p (rectSchurLambda p)
(rectSchurLambda_satisfies_threshold p) (rectSchurRecStep_mnp p)`; the `c' = 0` branch is the box-volume
bound. Now CLOSED (the real per-step `rectSchurRecStep_mnp`, no `sorry`). -/
theorem routeMBoxThresholdFinite_mnp (m n p : ℕ) :
    RouteMBoxThresholdFinite (![m, n, p] : Fin 3 → ℕ) := by
  intro c' hc'
  rw [routeMLayerBoxIntegral_mnp_eq m n p]
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand ^0 = 1, box volume finite.
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hmatvol : ∀ a b : ℕ, (volume (matBox a b 1) : ℝ≥0∞) < ⊤ := by
      intro a b
      have hcpt : IsCompact (matBox a b (1 : ℝ)) := by
        have heq : matBox a b (1 : ℝ)
            = Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b => Set.Icc (-(1 : ℝ)) 1)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    have hcalc : ∫⁻ A0 in matBox m n 1, ∫⁻ A1 in matBox n p 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
        = volume (matBox m n 1) * volume (matBox n p 1) := by
      calc ∫⁻ A0 in matBox m n 1, ∫⁻ A1 in matBox n p 1,
              ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
          = ∫⁻ _A0 in matBox m n 1, ∫⁻ _A1 in matBox n p 1, (1 : ℝ≥0∞) := by
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A0 _ => ?_)
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A1 _ => ?_)
            rw [hzero]; simp [Real.rpow_zero]
        _ = volume (matBox m n 1) * volume (matBox n p 1) := by
            simp only [setLIntegral_const, one_mul]; rw [mul_comm]
    rw [hcalc]
    exact ENNReal.mul_lt_top (hmatvol m n) (hmatvol n p)
  · -- 0 < c' < ½·minAdm = rectSchurLambda p m n: the rectangular core finiteness.
    have hlt : (c' : ℝ) < rectSchurLambda p m n := by rw [rectSchurLambda]; exact hc'
    have hrc : RectSchurCore m n p (c' : ℝ) 1 :=
      rectCore_schurGen_lt_top p (rectSchurLambda p) (rectSchurLambda_satisfies_threshold p)
        (rectSchurRecStep_mnp p) m n (c' : ℝ) hc0 hlt 1 one_pos
    rw [RectSchurCore] at hrc
    exact hrc

/-- **The general-`(M0,M1,M2)` `cover_le` UPPER leg.** The `IsRouteMCover.cover_le` field for `(![m,n,p])`
(`1 ≤ minAdm`), the asymmetric analog of `routeMLayerCover_coverLe_rrp`: compose `routeMLayerCover_hfin`
(whose `hbox` is `routeMBoxThresholdFinite_mnp`) + the banked RHS positivity `layerCover_rhs_ne_zero`, via
`routeM_coverLe_of_finiteness`. Now CLOSED — this is the general-`L=2` UPPER deliverable. -/
theorem routeMLayerCover_coverLe_mnp (m n p : ℕ) (hpos : 1 ≤ minAdm (![m, n, p] : Fin 3 → ℕ)) :
    ∀ c' : NNReal, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∫⁻ x in routeMBaseNbhd (![m, n, p] : Fin 3 → ℕ),
          ENNReal.ofReal (|routeMCore (![m, n, p] : Fin 3 → ℕ) x| ^ (-(c' : ℝ)))
        ≤ C * ∑ i : (routeLayerAtlas (![m, n, p] : Fin 3 → ℕ)).ι,
            ∫⁻ y in unitBox (layerD (![m, n, p] : Fin 3 → ℕ) i),
              ENNReal.ofReal (monomialIntegrand (layerD (![m, n, p] : Fin 3 → ℕ) i)
                (layerK (![m, n, p] : Fin 3 → ℕ) i)
                (layerH (![m, n, p] : Fin 3 → ℕ) i) (c' : ℝ) y) :=
  routeM_coverLe_of_finiteness (routeMCore (![m, n, p] : Fin 3 → ℕ))
    (routeMBaseNbhd (![m, n, p] : Fin 3 → ℕ))
    (layerD (![m, n, p] : Fin 3 → ℕ)) (layerK (![m, n, p] : Fin 3 → ℕ))
    (layerH (![m, n, p] : Fin 3 → ℕ))
    (layerCover_rhs_ne_zero (![m, n, p] : Fin 3 → ℕ))
    (routeMLayerCover_hfin (![m, n, p] : Fin 3 → ℕ) hpos (routeMBoxThresholdFinite_mnp m n p))

end DLNFibre.DLN.RLCT
