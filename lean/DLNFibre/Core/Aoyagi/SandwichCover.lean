import DLNFibre.Core.Aoyagi.ProductResolution

/-!
# `Core.Aoyagi.SandwichCover` — the R3 V-lower WIRE (abstract), `hideal_bwd`-FREE

The reroute V-lower cover assembly, `hideal_bwd`-FREE (the honest F10/(A) bypass). It is a bounded
adaptation of `Resolution.mem_localAdmissible_of_lt`: that lower-bound leg consumes the family-level
`hideal_bwd` at EXACTLY ONE line — the per-chart `IntegrableOn` of the pulled-back weighted loss
(via `Chart.integrableAtFilter_of_lt` → `wLocalAdmissible_swap`). Here that one input is supplied
by the SUM-level SANDWICH `cst·∑ (monomialₖ)² ≤ ∑ (Fᵢ∘g)²` (R2 survivor + `#172`), fed through the
banked one-directional `wLocalAdmissibleExponents_subset_of_eventually_le`. Everything else — the
area formula push-down (`lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null`), the
`integrableOn_finite_iUnion` subadditivity, and the `hcover` transfer onto a neighbourhood of `x₀` —
is ideal-free and reused verbatim.

Per-chart data is taken as LOOSE hypotheses (a `Chart` minus `hideal_fwd`/`hideal_bwd`, plus the
sandwich); the concrete `(3,3,4)` discharge supplies them from the flatCube geometry + R2 survivor,
NEVER from the retired α-atlas (`chartBridgeFaithful_buildTree`, `sorryAx`). Weakest-fields: only
the data the assembly USES is carried. In particular the squarefree binding `hunit1` (`e k₀ = 1` on
binding axes) is NOT a field here — the conclusion is stated at the `monomialThreshold`, which does
not read it; it is consumed only at the downstream `monomialThreshold → ½·minAdm` conversion
(Object D), where the `k = 1` / headline obligation lives.

`hbdd : BddAbove (localAdmissibleExponents (sumSqFam F) x₀)` IS a field, and it is load-bearing: the
sandwich is a LOWER bound only, so it cannot force `x₀` to be a genuine pole (`loss x₀ = 0`);
without it `localAdmissible = [0,∞)`, `sSup` collapses to the junk `0`, and `⨅ threshold ≤ 0` is
false. `BddAbove` is exactly the V-UPPER content (#110, `rlctAt ≤ ½·chartMin`), taken here as a
hypothesis and discharged downstream (one-directional — V-upper does not depend on V-lower).

## Scope
- IN: the abstract cover-assembly lower bound `⨅_c threshold_c ≤ rlctAt (∑Fᵢ²) x₀`, per-leaf
  obligations as hypotheses, `hideal_bwd`-free. `BddAbove` supplied by V-upper.
- OUT: the concrete `(3,3,4)` discharge of the per-leaf hypotheses (flatCube charts + survivor
  sandwich + `#172` + squarefree `hunit1`); Object D's `⨅ threshold = ½·minAdm`; V-upper `≤`-half.

## Main results
- `jacWeightForm_at_of_nbhd` — the loose-data carrier of the Jacobian normal form at a domain point
  (a globally-measurable `|unit|` factor); the `hideal`-free copy of `Chart.jacWeight_form_at`.
- `integrableAtFilter_of_sandwich` — per-point integrability of the weighted pulled-back loss from
  the SANDWICH (the one-line `hideal_bwd` replacement).
- `mem_localAdmissible_of_sandwich_lt` — the `BddAbove`-free membership core (the `hideal_bwd`-free
  analogue of `Resolution.mem_localAdmissible_of_lt`).
- `rlctAt_ge_iInf_threshold_of_sandwich_cover` — the V-lower headline `⨅_c threshold ≤ rlctAt`.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D Mn : ℕ}

/-- **Loose-data version of `Chart.jacWeight_form_at`** (`hideal`-free). On an open `nbhd` where the
absolute Jacobian `|det Dg|` factors as `jacWeight jac · |unit|` (`unit` continuous & nonvanishing
on `nbhd`), at every `p ∈ nbhd` there is a GLOBALLY measurable unit factor `um` (the piecewise
`|unit|`, extended by `1` off `nbhd`) realising the Jacobian normal form on a neighbourhood of `p`.
The carrier the engine (`monomialSumSq_integrableAtFilter_of_lt`) consumes at each `p`. -/
private lemma jacWeightForm_at_of_nbhd
    {g : (Fin D → ℝ) → (Fin D → ℝ)} {jac : Fin D → ℕ} {unit : (Fin D → ℝ) → ℝ}
    {nbhd : Set (Fin D → ℝ)} (hnbhd_open : IsOpen nbhd)
    (hunit_cont : ContinuousOn unit nbhd) (hunit_ne : ∀ u ∈ nbhd, unit u ≠ 0)
    (hjac : ∀ u ∈ nbhd, |jacDet g u| = jacWeight jac u * |unit u|)
    {p : Fin D → ℝ} (hp : p ∈ nbhd) :
    ∃ um : (Fin D → ℝ) → ℝ, ContinuousAt um p ∧ um p ≠ 0 ∧ Measurable um ∧
      ∀ᶠ u in 𝓝 p, |jacDet g u| = jacWeight jac u * um u := by
  classical
  have hnbhd_mem : nbhd ∈ 𝓝 p := hnbhd_open.mem_nhds hp
  set um : (Fin D → ℝ) → ℝ := Set.piecewise nbhd (fun u ↦ |unit u|) (fun _ ↦ 1) with hum
  have hum_eq : ∀ u ∈ nbhd, um u = |unit u| :=
    fun u hu ↦ Set.piecewise_eq_of_mem _ _ _ hu
  have hcabsOn : ContinuousOn (fun u ↦ |unit u|) nbhd := hunit_cont.abs
  have hum_meas : Measurable um := by
    apply measurable_of_isOpen
    intro t ht
    obtain ⟨v, v_open, hv⟩ : ∃ v : Set (Fin D → ℝ), IsOpen v ∧
        (fun u ↦ |unit u|) ⁻¹' t ∩ nbhd = v ∩ nbhd :=
      continuousOn_iff'.1 hcabsOn t ht
    rw [hum, Set.piecewise_preimage, Set.ite, hv]
    exact (v_open.measurableSet.inter hnbhd_open.measurableSet).union
      ((measurable_const ht.measurableSet).diff hnbhd_open.measurableSet)
  refine ⟨um, ?_, ?_, hum_meas, ?_⟩
  · have hum_ev : um =ᶠ[𝓝 p] fun u ↦ |unit u| := by
      filter_upwards [hnbhd_mem] with u hu using hum_eq u hu
    exact ((hunit_cont.continuousAt hnbhd_mem).abs).congr hum_ev.symm
  · rw [hum_eq p hp]; exact abs_ne_zero.mpr (hunit_ne p hp)
  · filter_upwards [hnbhd_mem] with u hu
    rw [hjac u hu, hum_eq u hu]

/-- **Per-point integrability of the weighted pulled-back loss, from the SANDWICH** (the one-line
`hideal_bwd` replacement). For `cc` below the chart's boxed threshold, the monomial convergence
engine (`monomialSumSq_integrableAtFilter_of_lt`) makes `cc` admissible against the monomial sum;
the SANDWICH `cst · ∑ₖ monomialₖ² ≤ L` (`cst > 0`) transfers that admissibility to the loss `L`
via the one-directional `wLocalAdmissibleExponents_subset_of_eventually_le` (a LARGER germ is MORE
integrable). No `hideal_bwd` / two-sided ideal swap — a plain domination. -/
theorem integrableAtFilter_of_sandwich
    {M' : ℕ} {W L : (Fin D → ℝ) → ℝ} {e : Fin M' → Fin D → ℕ} {jac : Fin D → ℕ} {k₀ : Fin M'}
    {um : (Fin D → ℝ) → ℝ} {p : Fin D → ℝ} {cst cc : ℝ}
    (hchain : ∀ k d, e k₀ d ≤ e k d) (hbind : (bindingAxes (e k₀)).Nonempty)
    (hlt : cc < monomialThreshold (e k₀) jac hbind) (hc0 : 0 ≤ cc) (hcst : 0 < cst)
    (hum_cont : ContinuousAt um p) (hum0 : um p ≠ 0) (hum_meas : Measurable um)
    (hW : ∀ᶠ u in 𝓝 p, W u = jacWeight jac u * um u)
    (hWmeas : Measurable W) (hWnn : ∀ᶠ w in 𝓝 p, 0 ≤ W w) (hLmeas : Measurable L)
    (hsandwich : ∀ᶠ u in 𝓝 p,
      0 ≤ cst * sumSqFam (monomialFam e) u ∧ cst * sumSqFam (monomialFam e) u ≤ L u) :
    IntegrableAtFilter (fun u ↦ W u * negPow L cc u) (𝓝 p) := by
  have hβ : ∀ d, -1 < (jac d : ℝ) - 2 * (e k₀ d : ℝ) * cc :=
    (monomial_forall_neg_one_lt_iff_lt_threshold e jac k₀ hbind cc).mpr hlt
  have hP : IntegrableAtFilter (fun u ↦ W u * negPow (sumSqFam (monomialFam e)) cc u) (𝓝 p) :=
    monomialSumSq_integrableAtFilter_of_lt hchain hβ hum_cont hum0 hum_meas hW
  -- admissible against the (positively scaled) monomial, then transferred to `L` by the sandwich.
  have hmemMono :
      cc ∈ wLocalAdmissibleExponents W (fun u ↦ cst * sumSqFam (monomialFam e) u) p := by
    rw [wLocalAdmissibleExponents_const_mul hcst]; exact ⟨hc0, hP⟩
  have hnull : LocallyNullZeros (fun u ↦ cst * sumSqFam (monomialFam e) u) p := by
    obtain ⟨s, hs, hnull0⟩ := locallyNullZeros_sumSqFam_monomialFam e k₀ p
    refine ⟨s, hs, measure_mono_null (fun w hw ↦ ?_) hnull0⟩
    exact Set.mem_inter ((mul_eq_zero.mp hw.1).resolve_left (ne_of_gt hcst)) hw.2
  have hsub := wLocalAdmissibleExponents_subset_of_eventually_le hWmeas hLmeas hWnn hsandwich hnull
  exact (hsub hmemMono).2

/-- **The `BddAbove`-free membership core** — the `hideal_bwd`-free analogue of
`Resolution.mem_localAdmissible_of_lt`. If `cc ≥ 0` is below EVERY chart's boxed threshold, then
`cc` is locally admissible for the loss `∑ Fᵢ²` at `x₀`. Bounded adaptation of the reference: the
per-chart `IntegrableOn` line (which there rode `hideal_bwd`) is here supplied by
`integrableAtFilter_of_sandwich` from the SANDWICH; the area-formula push-down, the
`integrableOn_finite_iUnion` subadditivity and the `hcover` transfer onto `U` are reused verbatim.
No `BddAbove` — a pure membership, the honest V-lower content (the `sSup`/`rlctAt` step lands
in `rlctAt_ge_iInf_threshold_of_sandwich_cover` with the V-upper `BddAbove`). -/
theorem mem_localAdmissible_of_sandwich_lt
    {F : Fin Mn → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ} {numCharts : ℕ}
    {g : Fin numCharts → (Fin D → ℝ) → (Fin D → ℝ)}
    {dom nbhd excep : Fin numCharts → Set (Fin D → ℝ)}
    {bexp : Fin numCharts → Fin Mn → Fin D → ℕ} {k₀ : Fin numCharts → Fin Mn}
    {jac : Fin numCharts → Fin D → ℕ} {unit : Fin numCharts → (Fin D → ℝ) → ℝ}
    {cst : Fin numCharts → ℝ} {U : Set (Fin D → ℝ)}
    (hbind : ∀ c, (bindingAxes (bexp c (k₀ c))).Nonempty)
    (hFmeas : ∀ i, Measurable (F i))
    (hgdiff : ∀ c, Differentiable ℝ (g c))
    (hdomcpt : ∀ c, IsCompact (dom c))
    (hnbhd_open : ∀ c, IsOpen (nbhd c)) (hdom_sub : ∀ c, dom c ⊆ nbhd c)
    (hexcep_meas : ∀ c, MeasurableSet (excep c)) (hexcep_null : ∀ c, volume (excep c) = 0)
    (hg_inj : ∀ c, Set.InjOn (g c) (nbhd c \ excep c))
    (hchain : ∀ c k d, bexp c (k₀ c) d ≤ bexp c k d)
    (hunit_cont : ∀ c, ContinuousOn (unit c) (nbhd c))
    (hunit_ne : ∀ c, ∀ u ∈ nbhd c, unit c u ≠ 0)
    (hjac : ∀ c, ∀ u ∈ nbhd c, |jacDet (g c) u| = jacWeight (jac c) u * |unit c u|)
    (hcst : ∀ c, 0 < cst c)
    (hsandwich : ∀ c, ∀ p ∈ dom c, ∀ᶠ w in 𝓝 p,
      0 ≤ cst c * sumSqFam (monomialFam (bexp c)) w ∧
        cst c * sumSqFam (monomialFam (bexp c)) w ≤ sumSqFam (fun i ↦ F i ∘ g c) w)
    (hU : U ∈ 𝓝 x₀) (hcover : volume (U \ ⋃ c, (g c) '' (dom c)) = 0)
    {cc : ℝ} (hc0 : 0 ≤ cc)
    (hlt : ∀ c, cc < monomialThreshold (bexp c (k₀ c)) (jac c) (hbind c)) :
    cc ∈ localAdmissibleExponents (sumSqFam F) x₀ := by
  refine ⟨hc0, ?_⟩
  -- each chart's image is integrable, via the area formula from the compact-domain integrability.
  have step1 : ∀ c, IntegrableOn (negPow (sumSqFam F) cc) ((g c) '' (dom c)) := by
    intro c
    have hgdiffc : Differentiable ℝ (g c) := hgdiff c
    have hdommeas : MeasurableSet (dom c) := (hdomcpt c).measurableSet
    have hg_inj_dom : Set.InjOn (g c) (dom c \ excep c) :=
      (hg_inj c).mono (Set.diff_subset_diff_left (hdom_sub c))
    -- the weight `|det Dg|` is measurable unconditionally (`measurable_fderiv`, then `det`, `abs`).
    have hWmeas : Measurable (fun u ↦ |jacDet (g c) u|) := by
      have h1 : Measurable (fun u ↦ (fderiv ℝ (g c) u).det) :=
        ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ (g c))
      exact h1.abs
    have hWnn : ∀ w, (0 : ℝ) ≤ |jacDet (g c) w| := fun w ↦ abs_nonneg _
    -- measurability of the pulled-back loss `∑ (Fᵢ∘g)²`.
    have hLmeas : Measurable (sumSqFam (fun i ↦ F i ∘ g c)) := by
      unfold sumSqFam
      exact Finset.measurable_sum _
        (fun i _ ↦ ((hFmeas i).comp hgdiffc.continuous.measurable).pow_const 2)
    -- compact-domain integrability of the pulled-back weighted loss, FROM THE SANDWICH.
    have hdom_int : IntegrableOn
        (fun u ↦ |jacDet (g c) u| * negPow (sumSqFam (fun i ↦ F i ∘ g c)) cc u) (dom c) := by
      apply LocallyIntegrableOn.integrableOn_isCompact ?_ (hdomcpt c)
      intro p hp
      obtain ⟨um, hum_cont, hum0, hum_meas, hWform⟩ :=
        jacWeightForm_at_of_nbhd (hnbhd_open c) (hunit_cont c) (hunit_ne c) (hjac c)
          (hdom_sub c hp)
      exact IntegrableAtFilter.filter_mono nhdsWithin_le_nhds
        (integrableAtFilter_of_sandwich (hchain c) (hbind c) (hlt c) hc0 (hcst c)
          hum_cont hum0 hum_meas hWform hWmeas (Filter.Eventually.of_forall hWnn) hLmeas
          (hsandwich c p hp))
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

/-- **R3 V-lower wire (abstract, `hideal_bwd`-free) — the headline.** Given a finite family of
resolution charts `g c` over compact domains `dom c` whose images a.e.-cover a neighbourhood `U` of
`x₀` (`hcover`), each carrying the area-formula data (`g c` differentiable, `dom c ⊆ nbhd c` open,
a.e.-injective off a null `excep c`, Jacobian `|det Dg| = jacWeight (jac c) · |unit c|` with
`unit c` continuous/nonzero on `nbhd c`), the divisibility chain `hchain`, and the SUM-level
SANDWICH `cst c · ∑ₖ (monomialₖ)² ≤ ∑ᵢ (Fᵢ∘g c)²` near each point of `dom c` — the RLCT of the loss
`∑ Fᵢ²` at `x₀` is at least the `min` over charts of the boxed threshold
`monomialThreshold (bexp c (k₀ c)) (jac c)`. NO `hideal_bwd`: the sandwich alone drives the
lower-bound `⊇`-direction (`wLocalAdmissibleExponents_subset_of_eventually_le`). `hbdd` (the genuine
pole at `x₀`, = V-upper #110) turns the membership `Ico 0 R ⊆ localAdmissible` into the
`sSup`/`rlctAt` inequality. -/
theorem rlctAt_ge_iInf_threshold_of_sandwich_cover
    {F : Fin Mn → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    {numCharts : ℕ} (hne : (Finset.univ : Finset (Fin numCharts)).Nonempty)
    (g : Fin numCharts → (Fin D → ℝ) → (Fin D → ℝ))
    (dom nbhd excep : Fin numCharts → Set (Fin D → ℝ))
    (bexp : Fin numCharts → Fin Mn → Fin D → ℕ) (k₀ : Fin numCharts → Fin Mn)
    (jac : Fin numCharts → Fin D → ℕ) (unit : Fin numCharts → (Fin D → ℝ) → ℝ)
    (cst : Fin numCharts → ℝ) (U : Set (Fin D → ℝ))
    (hbind : ∀ c, (bindingAxes (bexp c (k₀ c))).Nonempty)
    (hFmeas : ∀ i, Measurable (F i))
    (hgdiff : ∀ c, Differentiable ℝ (g c))
    (hdomcpt : ∀ c, IsCompact (dom c))
    (hnbhd_open : ∀ c, IsOpen (nbhd c)) (hdom_sub : ∀ c, dom c ⊆ nbhd c)
    (hexcep_meas : ∀ c, MeasurableSet (excep c)) (hexcep_null : ∀ c, volume (excep c) = 0)
    (hg_inj : ∀ c, Set.InjOn (g c) (nbhd c \ excep c))
    (hchain : ∀ c k d, bexp c (k₀ c) d ≤ bexp c k d)
    (hunit_cont : ∀ c, ContinuousOn (unit c) (nbhd c))
    (hunit_ne : ∀ c, ∀ u ∈ nbhd c, unit c u ≠ 0)
    (hjac : ∀ c, ∀ u ∈ nbhd c, |jacDet (g c) u| = jacWeight (jac c) u * |unit c u|)
    (hcst : ∀ c, 0 < cst c)
    (hsandwich : ∀ c, ∀ p ∈ dom c, ∀ᶠ w in 𝓝 p,
      0 ≤ cst c * sumSqFam (monomialFam (bexp c)) w ∧
        cst c * sumSqFam (monomialFam (bexp c)) w ≤ sumSqFam (fun i ↦ F i ∘ g c) w)
    (hU : U ∈ 𝓝 x₀)
    (hcover : volume (U \ ⋃ c, (g c) '' (dom c)) = 0)
    (hbdd : BddAbove (localAdmissibleExponents (sumSqFam F) x₀)) :
    Finset.univ.inf' hne (fun c ↦ monomialThreshold (bexp c (k₀ c)) (jac c) (hbind c))
      ≤ rlctAt (sumSqFam F) x₀ := by
  set R := Finset.univ.inf' hne (fun c ↦ monomialThreshold (bexp c (k₀ c)) (jac c) (hbind c))
    with hRdef
  have hRpos : 0 < R := by
    rw [hRdef, Finset.lt_inf'_iff]; exact fun c _ ↦ monomialThreshold_pos _ _ _
  -- the membership core gives `Ico 0 R ⊆ localAdmissible`; then `BddAbove` bridges to `sSup`.
  have hIco : Set.Ico 0 R ⊆ localAdmissibleExponents (sumSqFam F) x₀ := by
    intro cc hcc
    refine mem_localAdmissible_of_sandwich_lt hbind hFmeas hgdiff hdomcpt hnbhd_open hdom_sub
      hexcep_meas hexcep_null hg_inj hchain hunit_cont hunit_ne hjac hcst hsandwich hU hcover
      hcc.1 (fun c ↦ ?_)
    have hlt := hcc.2
    rw [hRdef, Finset.lt_inf'_iff] at hlt
    exact hlt c (Finset.mem_univ c)
  rw [rlctAt_def]
  calc R = sSup (Set.Ico 0 R) := (csSup_Ico hRpos).symm
    _ ≤ sSup (localAdmissibleExponents (sumSqFam F) x₀) :=
        csSup_le_csSup hbdd (Set.nonempty_Ico.mpr hRpos) hIco

end DLNFibre.Core.Aoyagi
