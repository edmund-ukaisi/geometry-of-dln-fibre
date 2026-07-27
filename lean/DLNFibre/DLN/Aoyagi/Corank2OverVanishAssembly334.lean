import DLNFibre.DLN.Aoyagi.Corank2Headline334
import DLNFibre.DLN.Aoyagi.Corank2OverVanish334

/-!
# `DLN.Aoyagi.Corank2OverVanishAssembly334` — the STEP-6 mechanism-heterogeneous assembly (PROVED)

The convergence point for the full-288 (3,3,4) V-lower headline. The whole-conjugate family covers a
neighbourhood of `0` (`NativeFan334.native_hcover`, transported through the folded `Ψ` on the
over-vanishing leaves via `OverVanish334.image_comp_blockShear_superset`); per chart, the weighted
pulled-back loss `|jacDet g_c| · (∑ᵢ (coreGenᵢ ∘ g_c)²)^{-cc}` is integrable for every `cc < 4`:

* **clean-144** — via the single-entry survivor `hentry` (`coreGen_{k0}∘g_c = ∏ w^{ek₀}`), the chain
  engine `monomialSumSq_integrableAtFilter_of_lt` gives the boxed threshold `≥ 9/2 > 4`;
* **over-vanishing-144** — via `OverVanish334.chart_integrableAtFilter_of_monoSumSq_dom`, the
  product engine gives `min(threshold(vm²), r/2) = 4`.

Both mechanisms produce the SAME per-chart integrability shape, so the assembly abstracts it as ONE
hypothesis `hint` and the two seats discharge it over their charts of the shared cover. With `hbdd`
(the genuine pole, `bddAbove_localAdmissible_coreGen334`) the `Ico 0 4 ⊆ localAdmissible` membership
lifts to `4 ≤ rlctAt`.

## Status
PROVED (clean-three): the headline `rlctAt_coreGen334_ge_four_of_perchart_integrable` is fully proved
— a refactor of `Core.Aoyagi.mem_localAdmissible_of_sandwich_lt`'s spine (area formula push-down +
`integrableOn_finite_iUnion` + the `hcover` transfer onto a neighbourhood + `csSup_le_csSup` with
`hbdd`), with the per-chart integrability taken as `hint` rather than derived from a sandwich. The two
leaf mechanisms discharge `hint` at the use site `OverVanishHeadline334.rlctAt_coreGen334_ge_four`
(clean-144 via the survivor `hentry`, over-vanishing-144 via the SoS engine); axiom footprint clean-three.
-/

open MeasureTheory Set Filter Topology Metric RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.OverVanishAssembly334

/-- **The `hint`-level membership core** — the mechanism-agnostic analogue of
`Core.Aoyagi.mem_localAdmissible_of_sandwich_lt`. If `cc ≥ 0` and, per chart `c` and per point
`p ∈ dom c`, the weighted pulled-back loss `|jacDet (g c)| · (∑ᵢ (Fᵢ∘g c)²)^{-cc}` is integrable near
`p` (`hint`), then `cc` is locally admissible for the loss `∑ Fᵢ²` at `x₀`. This is
`mem_localAdmissible_of_sandwich_lt`'s spine with its per-chart `IntegrableOn` line — which there rode
the SUM-level sandwich (`integrableAtFilter_of_sandwich`) — supplied DIRECTLY by `hint`; the
area-formula push-down (`lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null`), the
`integrableOn_finite_iUnion` subadditivity and the `hcover` transfer onto `U` are reused verbatim. It
consumes the SAME per-chart integrability shape the two step-6 seats produce (clean-144 via the
survivor `hentry`; over-vanishing-144 via `chart_integrableAtFilter_of_monoSumSq_dom`), so both
mechanisms discharge it uniformly. -/
private theorem mem_localAdmissible_of_perchart_integrable
    {D Mn : ℕ} {F : Fin Mn → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ} {numCharts : ℕ}
    {g : Fin numCharts → (Fin D → ℝ) → (Fin D → ℝ)}
    {dom nbhd excep : Fin numCharts → Set (Fin D → ℝ)}
    {U : Set (Fin D → ℝ)} {cc : ℝ}
    (hFmeas : ∀ i, Measurable (F i))
    (hgdiff : ∀ c, Differentiable ℝ (g c))
    (hdomcpt : ∀ c, IsCompact (dom c))
    (hdom_sub : ∀ c, dom c ⊆ nbhd c)
    (hexcep_meas : ∀ c, MeasurableSet (excep c)) (hexcep_null : ∀ c, volume (excep c) = 0)
    (hg_inj : ∀ c, Set.InjOn (g c) (nbhd c \ excep c))
    (hU : U ∈ 𝓝 x₀) (hcover : volume (U \ ⋃ c, (g c) '' (dom c)) = 0)
    (hc0 : 0 ≤ cc)
    (hint : ∀ c, ∀ p ∈ dom c,
      IntegrableAtFilter
        (fun u ↦ |jacDet (g c) u| * negPow (sumSqFam (fun i ↦ F i ∘ g c)) cc u) (𝓝 p)) :
    cc ∈ localAdmissibleExponents (sumSqFam F) x₀ := by
  refine ⟨hc0, ?_⟩
  -- each chart's image is integrable, via the area formula from the compact-domain integrability.
  have step1 : ∀ c, IntegrableOn (negPow (sumSqFam F) cc) ((g c) '' (dom c)) := by
    intro c
    have hgdiffc : Differentiable ℝ (g c) := hgdiff c
    have hdommeas : MeasurableSet (dom c) := (hdomcpt c).measurableSet
    have hg_inj_dom : Set.InjOn (g c) (dom c \ excep c) :=
      (hg_inj c).mono (Set.diff_subset_diff_left (hdom_sub c))
    -- compact-domain integrability of the pulled-back weighted loss, FROM `hint` (the seat's output).
    have hdom_int : IntegrableOn
        (fun u ↦ |jacDet (g c) u| * negPow (sumSqFam (fun i ↦ F i ∘ g c)) cc u) (dom c) := by
      apply LocallyIntegrableOn.integrableOn_isCompact ?_ (hdomcpt c)
      intro p hp
      exact IntegrableAtFilter.filter_mono nhdsWithin_le_nhds (hint c p hp)
    -- push down through the area formula, get a finite image lintegral.
    have hpt : ∀ u, ENNReal.ofReal |(fderiv ℝ (g c) u).det|
          * ENNReal.ofReal (negPow (sumSqFam F) cc ((g c) u))
        = ENNReal.ofReal (|jacDet (g c) u| * negPow (sumSqFam (fun i ↦ F i ∘ g c)) cc u) := by
      intro u
      rw [show |jacDet (g c) u| = |(fderiv ℝ (g c) u).det| from rfl,
        show negPow (sumSqFam (fun i ↦ F i ∘ g c)) cc u = negPow (sumSqFam F) cc ((g c) u) from by
          simp only [negPow_apply, sumSqFam, Function.comp_apply],
        ENNReal.ofReal_mul (abs_nonneg _)]
    have hfin : ∫⁻ x in (g c) '' (dom c), ENNReal.ofReal (negPow (sumSqFam F) cc x) < ⊤ := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null volume hdommeas hgdiffc
        (hexcep_meas c) (hexcep_null c) hg_inj_dom
        (fun x ↦ ENNReal.ofReal (negPow (sumSqFam F) cc x))]
      simp_rw [hpt]
      exact hdom_int.setLIntegral_lt_top
    have hKmeas : Measurable (sumSqFam F) := by
      unfold sumSqFam
      exact Finset.measurable_sum _ (fun i _ ↦ (hFmeas i).pow_const 2)
    have hnn : ∀ x, 0 ≤ negPow (sumSqFam F) cc x :=
      fun x ↦ negPow_nonneg (sumSqFam_nonneg _ _) cc
    exact ⟨(measurable_negPow hKmeas cc).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).mpr hfin⟩
  -- assemble over the finite atlas union and transfer onto `U` via `hcover`.
  set uc : Set (Fin D → ℝ) := ⋃ c, (g c) '' (dom c) with hucdef
  have hunion : IntegrableOn (negPow (sumSqFam F) cc) uc :=
    integrableOn_finite_iUnion.mpr step1
  set Uc : Set (Fin D → ℝ) := U ∩ uc with hUcdef
  have hUeq : U =ᵐ[volume] Uc := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null ?_ hcover, measure_mono_null ?_ (measure_empty (μ := volume))⟩
    · intro x hx
      refine ⟨hx.1, fun hxuc ↦ hx.2 ?_⟩
      rw [hUcdef]; exact Set.mem_inter hx.1 hxuc
    · intro x hx
      have hxUc : x ∈ Uc := hx.1
      rw [hUcdef] at hxUc
      exact absurd hxUc.1 hx.2
  have hUcint : IntegrableOn (negPow (sumSqFam F) cc) Uc := by
    rw [hUcdef]; exact hunion.mono_set Set.inter_subset_right
  exact ⟨U, hU, hUcint.congr_set_ae hUeq⟩

/-- **STEP 6 — the mechanism-heterogeneous (3,3,4) V-lower headline (PROVED).** Given a finite
chart family `g` over compact domains `dom` whose images a.e.-cover `ball 0 1` (`hcover`; the
full-288 whole-conjugate cover, `Ψ`-transported on the over-vanishing leaves), each carrying the
area-formula data (differentiable, `dom c ⊆ nbhd c` open, a.e.-injective off a null `excep c`), and
the UNIFORM per-chart per-point integrability `hint` of the weighted pulled-back loss for every
`cc ∈ Ico 0 4` (discharged: clean-144 via the survivor `hentry` → chain engine `≥ 9/2`;
over-vanishing-144 via `chart_integrableAtFilter_of_monoSumSq_dom` → `= 4`), the RLCT of the
`(3,3,4)` core loss at `0` is `≥ 4`. The spine is a refactor of
`mem_localAdmissible_of_sandwich_lt` (per-chart integrability taken as `hint`); `hbdd` =
`bddAbove_localAdmissible_coreGen334`. -/
theorem rlctAt_coreGen334_ge_four_of_perchart_integrable
    {numCharts : ℕ} (_hne : (Finset.univ : Finset (Fin numCharts)).Nonempty)
    (g : Fin numCharts → (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (dom nbhd excep : Fin numCharts → Set (Fin 21 → ℝ))
    (_hgdiff : ∀ c, Differentiable ℝ (g c))
    (_hdomcpt : ∀ c, IsCompact (dom c))
    (_hnbhd_open : ∀ c, IsOpen (nbhd c)) (_hdom_sub : ∀ c, dom c ⊆ nbhd c)
    (_hexcep_meas : ∀ c, MeasurableSet (excep c)) (_hexcep_null : ∀ c, volume (excep c) = 0)
    (_hg_inj : ∀ c, Set.InjOn (g c) (nbhd c \ excep c))
    (_hcover : volume (ball (0 : Fin 21 → ℝ) 1 \ ⋃ c, g c '' dom c) = 0)
    (_hint : ∀ c, ∀ p ∈ dom c, ∀ cc ∈ Set.Ico (0 : ℝ) 4,
      IntegrableAtFilter
        (fun u ↦ |jacDet (g c) u|
          * negPow (sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ g c)) cc u) (𝓝 p)) :
    (4 : ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) := by
  -- map: step6-assembly — refactor of `mem_localAdmissible_of_sandwich_lt`'s spine (area formula +
  -- finite-union subadditivity + `hcover` transfer to `𝓝 0` + `csSup_le_csSup` with `hbdd`), with
  -- per-chart integrability supplied by `hint` (clean-144 hentry / over-vanishing bridge).
  have hbdd := DLNFibre.DLN.Aoyagi.bddAbove_localAdmissible_coreGen334
  have hFmeas : ∀ i, Measurable (coreGen dvec eWrap i) := chart334.hFmeas
  -- every exponent below the value `4` is locally admissible (the `hint`-fed membership core).
  have hIco : Set.Ico (0 : ℝ) 4 ⊆
      localAdmissibleExponents (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) := by
    intro cc hcc
    exact mem_localAdmissible_of_perchart_integrable hFmeas _hgdiff _hdomcpt _hdom_sub
      _hexcep_meas _hexcep_null _hg_inj (Metric.ball_mem_nhds (0 : Fin 21 → ℝ) one_pos) _hcover
      hcc.1 (fun c p hp ↦ _hint c p hp cc hcc)
  -- `hbdd` (the genuine pole = V-upper #110) bridges `Ico 0 4 ⊆ localAdmissible` to `4 ≤ sSup`.
  rw [rlctAt_def]
  calc (4 : ℝ) = sSup (Set.Ico 0 4) := (csSup_Ico (show (0 : ℝ) < 4 by norm_num)).symm
    _ ≤ sSup (localAdmissibleExponents (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ)) :=
        csSup_le_csSup hbdd (Set.nonempty_Ico.mpr (by norm_num)) hIco

end DLNFibre.DLN.Aoyagi.OverVanishAssembly334
