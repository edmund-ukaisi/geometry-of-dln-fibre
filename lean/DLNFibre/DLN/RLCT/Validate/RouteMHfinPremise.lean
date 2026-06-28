import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverGE
import DLNFibre.DLN.RLCT.Validate.Case222Cover

/-!
# `RouteMHfinPremise` — the ∀M hfin premise-reduction (leaf-sum-finite ⟹ `c' < ½·minAdm M`)

The small glue between the threshold theorem `routeMCore_threshold_lt_top_of_box` (which needs the
hypothesis `c' < ½·minAdm M`) and the R1 cover assembler `routeMLayerCover_of_atoms`, whose `hfin`
field consumes the bound in a *premise* shape:

    (∑ leaf, ∫_{unitBox} monomialIntegrand …^{−c'}) < ⊤  →  ∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} < ⊤.

The bridge is the **premise reduction** `layerCover_leafSum_lt_top_imp_lt_half_minAdm`:
*if the layer leaf-sum is finite then `c' < ½·minAdm M`*. Its contrapositive is the achiever-leaf
divergence — at `c' ≥ ½·minAdm M` the achiever leaf (`foldDivisors [minAdm M]`, a single binding
codim-`minAdm M` divisor) has `monomialThreshold = ½·minAdm M ≤ c'`, so its `unitBox` box integral is
`⊤` (`monomialIntegrand_lintegral_box_eq_top`), forcing the sum to `⊤`. The ∀M generalisation of the
`(2,2,2)`-specific first half of `routeM222_below_threshold_fin` (`Case222RouteMCover.lean`).

Combined with `routeMCore_threshold_lt_top_of_box` (gated on `RouteMBoxThresholdFinite M`, the genuine
analytic content), this yields `layerCover_hfin_of_box` — the `hfin` field in exactly the shape
`routeMLayerCover_of_atoms` consumes, modulo the named box-finiteness hypothesis.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **A single-divisor fold has a binding monomial.** `foldDivisors [c]` appends one pivot divisor to
the empty leaf, giving `k = Fin.snoc (fun _ => 0) 1` over the one axis, so its `0`-th entry is `1 ≠ 0`.
The `∃ j, k j ≠ 0` premise (the codim-`c` pivot divisor is the binding axis). MonoData-level (no
dependent atlas index), so it transports cleanly to the achiever leaf. -/
theorem foldDivisors_singleton_k_binding (c : ℕ) :
    (MonoData.foldDivisors [c]).k ⟨0, by simp [MonoData.foldDivisors, MonoData.appendDivisor]⟩ ≠ 0 := by
  -- (foldDivisors [c]).k = (appendDivisor (leafMonoData 0) c).k = Fin.snoc (fun _ => 0) 1
  show ((leafMonoData 0).appendDivisor c).k ⟨0, by simp [MonoData.appendDivisor]⟩ ≠ 0
  simp only [MonoData.appendDivisor, leafMonoData]
  rw [show (⟨0, by simp⟩ : Fin (0 + 1)) = Fin.last 0 from rfl, Fin.snoc_last]
  norm_num

/-- **The achiever leaf has a binding monomial.** The achiever leaf of the layer atlas is the
single-divisor fold `foldDivisors [layerLeafMin M 0]`; via `foldDivisors_singleton_k_binding` its `k`
has a nonzero entry. The `∃ j, layerK M i j ≠ 0` premise `monomialIntegrand_lintegral_box_eq_top` needs.
Transports the MonoData-level fact through the `data i = foldDivisors […]` equation by `subst`
(rewriting the dependent `layerD`/`layerK` together). -/
theorem layerK_achiever_binding (M : Fin (L + 1) → ℕ) (i : (routeLayerAtlas M).ι)
    (hi : (routeLayerAtlas M).data i = MonoData.foldDivisors [layerLeafMin M 0]) :
    ∃ j : Fin (layerD M i), layerK M i j ≠ 0 := by
  -- `layerD M i` and `layerK M i` both read `(routeLayerAtlas M).data i`; `hi` rewrites the shared base.
  unfold layerD layerK
  rw [hi]
  exact ⟨_, foldDivisors_singleton_k_binding (layerLeafMin M 0)⟩

/-- **The premise reduction (∀M): finite leaf-sum ⟹ `c' < ½·minAdm M`.** If the layer leaf-sum of the
weighted-monomial box integrals is finite, then `c' < ½·minAdm M`. Contrapositive: at `c' ≥ ½·minAdm M`
the achiever leaf (threshold `= ½·minAdm M ≤ c'`, binding monomial) has box integral `⊤`
(`monomialIntegrand_lintegral_box_eq_top`), so the sum (a `Finset.sum` of `≥ 0` terms with that term
`= ⊤`) is `⊤`, contradicting finiteness. The ∀M generalisation of `routeM222_below_threshold_fin`'s
`hc'lt` step. -/
theorem layerCover_leafSum_lt_top_imp_lt_half_minAdm (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal)
    (hB : (∑ i : (routeLayerAtlas M).ι, ∫⁻ y in unitBox (layerD M i),
        ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y)) < ⊤) :
    (c' : ℝ) < (minAdm M : ℝ) / 2 := by
  by_contra hge
  rw [not_lt] at hge
  -- `0 < c'` (since `½·minAdm M > 0`).
  have hhalf_pos : (0 : ℝ) < (minAdm M : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (minAdm M : ℝ) := by exact_mod_cast hpos
    linarith
  have hc'0 : (0 : ℝ) < (c' : ℝ) := lt_of_lt_of_le hhalf_pos hge
  -- pick the achiever leaf: `data i = foldDivisors [layerLeafMin M 0]`, threshold `= ½·minAdm M`.
  -- `routeLayerAtlas M := routeLayerAtlasAcc M 0` (defeq); ascribe the existential to the FOLDED `ι` so
  -- `i` and `hi` live in `(routeLayerAtlas M).ι` and the leaf-sum's `Fintype`/index match syntactically.
  obtain ⟨i, hi⟩ : ∃ i : (routeLayerAtlas M).ι,
      (routeLayerAtlas M).data i = MonoData.foldDivisors [layerLeafMin M 0] :=
    routeLayerAtlasAcc_achiever M 0
  have hmin0 : layerLeafMin M 0 = minAdm M := by rw [layerLeafMin_eq]; omega
  have hthr_i : monomialThreshold (layerD M i) (layerK M i) (layerH M i)
      = (minAdm M : ℝ≥0∞) / 2 := by
    unfold layerD layerK layerH
    rw [show ((routeLayerAtlas M).data i) = MonoData.foldDivisors [layerLeafMin M 0] from hi, hmin0]
    exact monomialThreshold_singleton (minAdm M) hpos
  -- `monomialThreshold (achiever) = ½·minAdm M ≤ ofReal c'`.
  have hle_thr : monomialThreshold (layerD M i) (layerK M i) (layerH M i)
      ≤ ENNReal.ofReal (c' : ℝ) := by
    rw [hthr_i]
    -- `½·minAdm M ≤ ofReal c'` from `½·minAdm M ≤ c'` (ℝ) via `ofReal`.
    have hofr : (minAdm M : ℝ≥0∞) / 2 = ENNReal.ofReal ((minAdm M : ℝ) / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_natCast]; norm_num
    rw [hofr]
    exact ENNReal.ofReal_le_ofReal hge
  -- the achiever leaf has a binding monomial.
  obtain ⟨j, hj⟩ := layerK_achiever_binding M i hi
  -- so the achiever box integral diverges (= ⊤).
  have htop : ∫⁻ y in unitBox (layerD M i),
      ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y) = ⊤ := by
    rw [show unitBox (layerD M i)
        = Set.univ.pi (fun _ : Fin (layerD M i) => Set.Icc (0 : ℝ) 1) from rfl]
    rw [← monomialIntegrand_lintegral_box_eq_top (layerD M i) (layerK M i) (layerH M i)
      ⟨j, hj⟩ (c' : ℝ) hle_thr hc'0 (show (0:ℝ) < 1 by norm_num)]
    refine setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (fun y _ => ?_)
    rw [abs_of_nonneg (by unfold monomialIntegrand; positivity)]
  -- the `i`-th term of the leaf-sum is `⊤`, so the whole sum is `⊤` — contradiction.
  have hsum_top : (∑ i' : (routeLayerAtlas M).ι, ∫⁻ y in unitBox (layerD M i'),
      ENNReal.ofReal (monomialIntegrand (layerD M i') (layerK M i') (layerH M i') (c' : ℝ) y)) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← htop]
    exact Finset.single_le_sum (f := fun i' => ∫⁻ y in unitBox (layerD M i'),
        ENNReal.ofReal (monomialIntegrand (layerD M i') (layerK M i') (layerH M i') (c' : ℝ) y))
      (fun i' _ => zero_le _) (Finset.mem_univ i)
  rw [hsum_top] at hB
  exact absurd hB (lt_irrefl _)

/-- **The `hfin` field, GIVEN the box finiteness (∀M).** In exactly the shape
`routeMLayerCover_of_atoms` consumes: whenever the layer leaf-sum is finite,
`∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} < ⊤`. The premise reduction
(`layerCover_leafSum_lt_top_imp_lt_half_minAdm`) turns the leaf-sum finiteness into `c' < ½·minAdm M`,
then `routeMCore_threshold_lt_top_of_box` (gated on `hbox : RouteMBoxThresholdFinite M`, the genuine
analytic content) closes it. The ∀M generalisation of the `(2,2,2)`-specific
`routeM222_below_threshold_fin` (`Case222RouteMCover.lean`), with the box-finiteness made an explicit,
named hypothesis. Feeds `routeMLayerCover_of_atoms`'s `hfin` field directly. -/
theorem layerCover_hfin_of_box (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (hbox : RouteMBoxThresholdFinite M) :
    ∀ c' : NNReal,
      (∑ i : (routeLayerAtlas M).ι, ∫⁻ y in unitBox (layerD M i),
          ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y)) < ⊤ →
      ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) < ⊤ := by
  intro c' hB
  exact routeMCore_threshold_lt_top_of_box M hbox c'
    (layerCover_leafSum_lt_top_imp_lt_half_minAdm M hpos c' hB)

end DLNFibre.DLN.RLCT
