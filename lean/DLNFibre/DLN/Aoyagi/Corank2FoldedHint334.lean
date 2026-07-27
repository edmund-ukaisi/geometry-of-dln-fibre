import DLNFibre.DLN.Aoyagi.Corank2FoldedFamily334

/-!
# `DLN.Aoyagi.Corank2FoldedHint334` — the per-chart INTEGRABILITY leaf (discharge (c) ⊕ (b))

The `hint` obligation of the (3,3,4) V-lower headline (`Corank2OverVanishHeadline334`): for EVERY
folded chart `gFold c` — clean-144 or over-vanishing-144 — and every `cc ∈ [0,4)`, the weighted
pulled-back loss `|jacDet (gFold c)| · (∑ᵢ (coreGenᵢ ∘ gFold c)²)^{-cc}` is integrable near each base
point. The single deliverable `folded_hint` is exactly the type the skeleton's `case hint` hole needs
(`exact folded_hint`).

Two branches (`by_cases IsClean c`):

* **CLEAN** (`IsClean c`) — `gFold c = gFin c ∘ id = gFin c`, so the clean-144 seat
  `CleanIntegrable334.clean_hint` (survivor entry `→` chain engine, boxed threshold `≥ 9/2`) serves
  it verbatim after `rw [gFold = gFin]`.

* **OVER-VANISHING** (`¬IsClean c`) — the over-vanishing bridge
  `OverVanish334.chart_integrableAtFilter_of_monoSumSq_dom` (product engine, value `min(threshold,
  |Z|/2) = 4`), fed the folded data `(a, Z, jac)` transported by the loss-symmetry permutation
  `σ_{p1}` from the base type `bundleAt c`:
  - `hW` — the foundation's `folded_jac_collapse` (`|jacDet (gFold c)| = jacWeight (jacExpFold c)`);
  - `hdom` (`folded_domination`, helper (3)) — `gFold_over_eq` + `OverVanishTransport334.domination_transport`
    (9-way `p1` dispatch, `loss_symm_sigOf`/`sigOf_symm`) + the base `bundleOf_domination`;
  - the threshold facts — the 16 canonical per-type data facts (`bundleOf_*`, `decide`), transported
    by the coordinate-permutation reindex (`bindingAxes_reindex`, `monomialThreshold` reindex-invariance
    packaged into `four_le_monomialThreshold_of`), giving `min(monomialThreshold ≥ 4, |Z|/2 = 4) ≥ 4`
    so every `cc < 4` is admissible.
-/

open MeasureTheory Set Filter Topology Metric RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.NativeJac334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
open DLNFibre.DLN.Aoyagi.CleanHentry334

namespace DLNFibre.DLN.Aoyagi.OverVanishHeadline334

/-! ## §1 — the 16 canonical per-type data facts (base-type `decide`) -/

set_option maxRecDepth 8000 in
/-- **Every base type's regular-sequence block has 8 coordinates.** -/
theorem bundleOf_Z_card (q r : Fin 21) : (bundleOf q r).Z.card = 8 := by
  simp only [bundleOf]; split_ifs <;> decide

set_option maxRecDepth 8000 in
/-- **Every base type's regular-sequence block is nonempty.** -/
theorem bundleOf_Z_ne (q r : Fin 21) : (bundleOf q r).Z.Nonempty := by
  rw [← Finset.card_pos, bundleOf_Z_card]; norm_num

set_option maxRecDepth 8000 in
/-- **The dominant monomial vanishes on the regular-sequence block.** -/
theorem bundleOf_Za (q r : Fin 21) : ∀ j ∈ (bundleOf q r).Z, (bundleOf q r).a j = 0 := by
  simp only [bundleOf]; split_ifs <;> decide

set_option maxRecDepth 8000 in
/-- **The Jacobian exponent vanishes on the regular-sequence block.** -/
theorem bundleOf_Zjac (q r : Fin 21) : ∀ j ∈ (bundleOf q r).Z, (bundleOf q r).jac j = 0 := by
  simp only [bundleOf]; split_ifs <;> decide

set_option maxRecDepth 8000 in
/-- **The dominant pivot `20` is a binding axis of every base type** (so `bindingAxes` is
nonempty). -/
theorem bundleOf_binding_ne (q r : Fin 21) : (bindingAxes (bundleOf q r).a).Nonempty := by
  refine ⟨20, ?_⟩
  simp only [bundleOf, bindingAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> decide

set_option maxRecDepth 8000 in
/-- **On every binding axis the dominant monomial is squarefree (`= 1`) and the Jacobian exponent is
`≥ 7`.** The over-vanishing analogue of `CleanIntegrable334.jacFin_ge_seven_on_binding`: the binding
axes are the pivot cross `{p1, p2, p3}`, where `jacExp` is `8` (at `p1`) or `≥ 7` (at `p2`, and at
`p3` via the `p2 ∈ σC2(p1)` inner blow-up). -/
theorem bundleOf_binding (q r : Fin 21) :
    ∀ e ∈ bindingAxes (bundleOf q r).a, (bundleOf q r).a e = 1 ∧ 7 ≤ (bundleOf q r).jac e := by
  simp only [bundleOf]; split_ifs <;> decide

/-! ## §2 — the coordinate-permutation reindex of the boxed threshold -/

/-- **The binding axes reindex under a coordinate permutation.** `bindingAxes (a ∘ σ⁻¹) = σ ''
bindingAxes a`. -/
theorem bindingAxes_reindex (σ : Equiv.Perm (Fin 21)) (a : Fin 21 → ℕ) :
    bindingAxes (fun d ↦ a (σ.symm d)) = (bindingAxes a).image σ := by
  ext d
  simp only [bindingAxes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hd; exact ⟨σ.symm d, hd, σ.apply_symm_apply d⟩
  · rintro ⟨e, he, rfl⟩; rwa [σ.symm_apply_apply]

/-- **The boxed threshold is `≥ 4` from the binding-axis facts.** If on every binding axis the
dominant monomial exponent is `1` and the Jacobian exponent is `≥ 7`, then each boxed ratio
`(jac_d + 1)/(2·a_d) ≥ 4`, hence their `inf'`. (Mirrors `CleanIntegrable334.four_le_monomialThreshold`,
generic over `a`, `jac`.) -/
theorem four_le_monomialThreshold_of {a jac : Fin 21 → ℕ} (hbind : (bindingAxes a).Nonempty)
    (h : ∀ d ∈ bindingAxes a, a d = 1 ∧ 7 ≤ jac d) :
    (4 : ℝ) ≤ monomialThreshold a jac hbind := by
  unfold monomialThreshold
  refine Finset.le_inf' hbind _ (fun d hd => ?_)
  obtain ⟨ha, hj⟩ := h d hd
  have hcast : ((a d : ℕ) : ℝ) = 1 := by rw [ha]; norm_num
  have hjR : (7 : ℝ) ≤ (jac d : ℝ) := by exact_mod_cast hj
  rw [hcast, mul_one]
  linarith

/-! ## §3 — the 9-way loss-symmetry dispatch for `σ_{p1}` -/

/-- **`σ_{p1}` is an involution** (`σ⁻¹ = σ`) for every dominant pivot `p1 ∈ S1`. -/
theorem sigOf_symm (p1 : Fin 21) (hp1 : p1 ∈ S1) : (sigOf p1).symm = sigOf p1 := by
  fin_cases hp1 <;> rfl

/-- **`σ_{p1}` is a loss symmetry** for every dominant pivot `p1 ∈ S1` (the 8 `loss_symm_P{n}` plus the
identity at `p1 = 20`). -/
theorem loss_symm_sigOf (p1 : Fin 21) (hp1 : p1 ∈ S1) (w : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k (fun t ↦ w (sigOf p1 t))) ^ 2)
      = ∑ k, (coreGen dvec eWrap k w) ^ 2 := by
  -- `S1 = {0,1,2,3,4,5,6,7,20}`; dispatch in that order (a blind `first` over the 8 `loss_symm_P{n}`
  -- forces a heavy `coreGen`-sum `whnf` per failed alternative and times out — see the ordered form).
  fin_cases hp1
  · exact OverVanishTransport334.loss_symm_P0 w
  · exact OverVanishTransport334.loss_symm_P1 w
  · exact OverVanishTransport334.loss_symm_P2 w
  · exact OverVanishTransport334.loss_symm_P3 w
  · exact OverVanishTransport334.loss_symm_P4 w
  · exact OverVanishTransport334.loss_symm_P5 w
  · exact OverVanishTransport334.loss_symm_P6 w
  · exact OverVanishTransport334.loss_symm_P7 w
  · simp only [show sigOf 20 = Equiv.refl (Fin 21) from rfl, Equiv.refl_apply]

/-! ## §4 — the folded-chart domination (helper (3)) -/

/-- **The folded-chart product-germ domination.** The over-vanishing folded chart `gFold c` dominates
the `σ_{p1}`-transported product germ `monoSumSqGerm (a ∘ σ⁻¹) (σ Z)` of its base type. `gFold_over_eq`
presents `gFold c` as the `σ_{p1}`-conjugate of the base composite; `domination_transport` (9-way
`p1`, `loss_symm_sigOf`/`sigOf_symm`) transports the base `bundleOf_domination`. -/
theorem folded_domination (c : Fin numCharts) (hc : ¬ IsClean c) (u : Fin 21 → ℝ) :
    monoSumSqGerm (fun d ↦ (bundleAt c).a ((sigOf (p1Of c)).symm d))
        ((bundleAt c).Z.image (sigOf (p1Of c))) u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ gFold c) u := by
  rw [gFold_over_eq c hc]
  exact OverVanishTransport334.domination_transport (sigOf (p1Of c))
    (sigOf_symm (p1Of c) (idxEquiv c).1.2)
    (loss_symm_sigOf (p1Of c) (idxEquiv c).1.2)
    (gFlat (bundleAt c).idxC ∘ (bundleAt c).psi)
    (bundleAt c).a (bundleAt c).Z
    (bundleOf_domination (canonQ c) (canonR c)) u

/-! ## §5 — the per-chart integrability leaf -/

set_option maxHeartbeats 800000 in
-- the over-vanishing branch wires a large `σ_{p1}`-transported composite through the product engine;
-- the default budget is tight, so raise it.
/-- **The per-chart integrability leaf `folded_hint`.** For every folded chart `gFold c` (clean or
over-vanishing) and every `cc ∈ [0,4)`, the weighted pulled-back loss is integrable near each base
point. The exact type the skeleton's `case hint` hole consumes. -/
theorem folded_hint : ∀ c, ∀ p ∈ domFold c, ∀ cc ∈ Set.Ico (0 : ℝ) 4,
    IntegrableAtFilter
      (fun u ↦ |jacDet (gFold c) u|
        * negPow (sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ gFold c)) cc u) (𝓝 p) := by
  intro c p _hp cc hcc
  by_cases hc : IsClean c
  · -- CLEAN branch — `gFold c = gFin c`, serve via `clean_hint`.
    have hg : gFold c = gFin c := by
      simp only [gFold, psiOf, if_pos hc, Function.comp_id]
    rw [hg]
    exact CleanIntegrable334.clean_hint c hc p cc hcc
  · -- OVER-VANISHING branch — the `σ_{p1}`-transported product-engine bridge.
    have hbind' : (bindingAxes (fun d ↦ (bundleAt c).a ((sigOf (p1Of c)).symm d))).Nonempty := by
      rw [bindingAxes_reindex]
      exact (bundleOf_binding_ne (canonQ c) (canonR c)).image (sigOf (p1Of c))
    have hjaceq : jacExpFold c = fun d ↦ (bundleAt c).jac ((sigOf (p1Of c)).symm d) := by
      simp only [jacExpFold, if_neg hc]
    have hthr' : cc < monomialThreshold (fun d ↦ (bundleAt c).a ((sigOf (p1Of c)).symm d))
        (jacExpFold c) hbind' := by
      refine lt_of_lt_of_le hcc.2 ?_
      rw [hjaceq]
      refine four_le_monomialThreshold_of hbind' (fun d hd => ?_)
      rw [bindingAxes_reindex, Finset.mem_image] at hd
      obtain ⟨e, he, rfl⟩ := hd
      simp only [Equiv.symm_apply_apply]
      exact bundleOf_binding (canonQ c) (canonR c) e he
    have hZa' : ∀ j ∈ (bundleAt c).Z.image (sigOf (p1Of c)),
        (fun d ↦ (bundleAt c).a ((sigOf (p1Of c)).symm d)) j = 0 := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨z, hz, rfl⟩ := hj
      simp only [Equiv.symm_apply_apply]
      exact bundleOf_Za (canonQ c) (canonR c) z hz
    have hZjac' : ∀ j ∈ (bundleAt c).Z.image (sigOf (p1Of c)), jacExpFold c j = 0 := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨z, hz, rfl⟩ := hj
      rw [hjaceq]
      simp only [Equiv.symm_apply_apply]
      exact bundleOf_Zjac (canonQ c) (canonR c) z hz
    have hZne' : ((bundleAt c).Z.image (sigOf (p1Of c))).Nonempty :=
      (bundleOf_Z_ne (canonQ c) (canonR c)).image (sigOf (p1Of c))
    have hZcard' : ((bundleAt c).Z.image (sigOf (p1Of c))).card = 8 := by
      rw [Finset.card_image_of_injective _ (sigOf (p1Of c)).injective]
      exact bundleOf_Z_card (canonQ c) (canonR c)
    have hsos' : 2 * cc < (((bundleAt c).Z.image (sigOf (p1Of c))).card : ℝ) := by
      rw [hZcard']; push_cast; linarith [hcc.2]
    have hdom' : ∀ᶠ u in 𝓝 p,
        monoSumSqGerm (fun d ↦ (bundleAt c).a ((sigOf (p1Of c)).symm d))
            ((bundleAt c).Z.image (sigOf (p1Of c))) u
          ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ gFold c) u :=
      Filter.Eventually.of_forall (folded_domination c hc)
    exact OverVanish334.chart_integrableAtFilter_of_monoSumSq_dom
      hbind' hZne' hZa' hZjac' hcc.1 hthr' hsos'
      (fun i ↦ (continuous_coreGen dvec eWrap i).measurable)
      (differentiable_gFold c).continuous.measurable
      (folded_jac_collapse c) hdom'

end DLNFibre.DLN.Aoyagi.OverVanishHeadline334
