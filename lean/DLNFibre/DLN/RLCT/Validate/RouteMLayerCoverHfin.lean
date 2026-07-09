import DLNFibre.DLN.RLCT.Validate.RouteMLayerCover
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.MonomialThresholdIdentity

/-!
# `RouteMLayerCoverHfin` — the `cover_le` UPPER leg (below-threshold finiteness), general `M`

The `hfin` atom of `routeMLayerCover_of_atoms` (the UPPER/finiteness leg of the general-`M`
`IsRouteMCover` over the layer atlas), R1 critical-path. SPEC-FIRST traced the objects and found the
honest shape (decorrelated-Codex-confirmed, 2026-06-30):

## The value-only layer atlas (the SPECIFY revision)

`routeLayerAtlas M` is a **value-only** chart family — each leaf `i` carries `MonoData.foldDivisors
[cᵢ]`, a synthetic single-divisor 1-D monomial `(d=1, k=[1], h=[cᵢ−1])` whose only content is the
threshold value `cᵢ/2 = ½·(path codim)`. There is **no geometric chart map `φᵢ`** from `routeMCore M`
to the leaves; the family carries zero measure-theoretic information about the loss. Consequently the
SPEC's envisioned "per-chart change-of-variables" (sub-lemma 2) does NOT exist — there are no charts to
do a c-o-v on — and the leaf-sum-finiteness hypothesis delivers ONLY the numerical bound
`(c':ℝ) < ½·minAdm M`.

The genuine plumbing from `routeMCore M` to a box integral is the SORRY-FREE general-`M`
`routeMCore_le_matBox` (`RouteMBoxReduction.lean`), whose RHS is the FULL layer-product box integral
`routeMLayerBoxIntegral M c' 1` — NOT the leaf-sum. Its finiteness below threshold is the named
`RouteMBoxThresholdFinite M`, the **genuine open analytic content** of the upper bound (discharged only
for the depth-2 `(r,r,p)` family; for general/deeper `M` it is the documented open gap). So an
UNCONDITIONAL general-`M` `hfin` is not reachable with the current sorry-free toolkit — it secretly
requires `RouteMBoxThresholdFinite M`. This file therefore states `hfin` with `hbox :
RouteMBoxThresholdFinite M` as an **explicit hypothesis** (precision discipline: the upper leg is
"assembled sorry-free MODULO the named `RouteMBoxThresholdFinite M`", not a hidden `sorry`).

## What this banks (sorry-free, axioms = `[propext, Classical.choice, Quot.sound, monomial_rlct]`)

1. `layerCover_leafSum_lt_top_imp_lt_half_minAdm` — the genuine **completeness / "no missing strata"**:
   leaf-sum finite at `c'` ⟹ `(c':ℝ) < ½·minAdm M` (for `1 ≤ minAdm M`). The achiever leaf
   (`data = foldDivisors [minAdm M]`, threshold `= ½·minAdm M`, with a binding axis `k 0 = 1 ≠ 0`)
   would have its `unitBox` integral `= ⊤` whenever `c' ≥ ½·minAdm M`
   (`monomialIntegrand_lintegral_box_eq_top`, the `monomial_rlct`/S2 divergence), so the sum would be
   `⊤` — contrapositive. This is sub-lemma 1's real content; the chainRel-descent the SPEC feared is
   unnecessary (one banked achiever-leaf witness suffices).
2. `routeMLayerCover_hfin` — the `hfin` atom: assemble (1) `⟹ c' < ½·minAdm M` then the banked
   `routeMCore_threshold_lt_top_of_box M hbox` (`c'=0` edge + the `routeMCore_le_matBox` box reduction).
-/

open MeasureTheory
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- A single-divisor leaf `foldDivisors [c]` has a binding axis (`k 0 = 1 ≠ 0`): the synthetic monomial
`(d=1, k=[1], h=[c−1])` is genuinely singular, so the threshold-divergence machinery
(`monomialIntegrand_lintegral_box_eq_top`) applies to it. -/
theorem foldDivisors_singleton_k_ne_zero (c : ℕ) :
    ∃ j, (MonoData.foldDivisors [c]).k j ≠ 0 := by
  refine ⟨⟨0, by simp [MonoData.foldDivisors, MonoData.appendDivisor, leafMonoData]⟩, ?_⟩
  simp [MonoData.foldDivisors, MonoData.appendDivisor, leafMonoData, Fin.snoc]

/-- **Sub-lemma 1 (COMPLETENESS — "no missing strata").** If the layer-atlas leaf-sum of per-leaf
monomial integrals is finite at `c'`, then `(c':ℝ) < ½·minAdm M` (for non-degenerate `1 ≤ minAdm M`).
The contrapositive of the achiever-leaf divergence: the achiever leaf `i₀` carries
`data i₀ = foldDivisors [minAdm M]`, with `monomialThreshold = ½·minAdm M` (`monomialThreshold_singleton`)
and a binding axis (`foldDivisors_singleton_k_ne_zero`). If `c' ≥ ½·minAdm M` then `c'` is at-or-above
that leaf's threshold, so its `unitBox = [0,1]^d` integral is `⊤` (`monomialIntegrand_lintegral_box_eq_top`
at `ε=1`; the integrand is `≥ 0`, so `ofReal = ofReal|·|`), forcing the sum to `⊤` — contradicting the
hypothesis. The genuine cover-completeness content of the upper leg; rides the cited S2 `monomial_rlct`. -/
theorem layerCover_leafSum_lt_top_imp_lt_half_minAdm (M : Fin (L + 1) → ℕ)
    (hpos : 1 ≤ minAdm M) (c' : NNReal)
    (hsum : (∑ i : (routeLayerAtlas M).ι, ∫⁻ y in unitBox (layerD M i),
        ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y)) < ⊤) :
    (c' : ℝ) < (minAdm M : ℝ) / 2 := by
  by_contra hge
  rw [not_lt] at hge
  obtain ⟨i₀', hi₀⟩ := routeLayerAtlasAcc_achiever M 0
  -- the achiever index, in the canonical `(routeLayerAtlas M).ι` type/instance.
  let i₀ : (routeLayerAtlas M).ι := i₀'
  have hmin0 : layerLeafMin M 0 = minAdm M := by rw [layerLeafMin_eq]; omega
  rw [hmin0] at hi₀
  have hdata : (routeLayerAtlas M).data i₀ = MonoData.foldDivisors [minAdm M] := hi₀
  -- the achiever leaf's threshold is `½·minAdm M`.
  have hthr : monomialThreshold (layerD M i₀) (layerK M i₀) (layerH M i₀) = (minAdm M : ℝ≥0∞) / 2 := by
    unfold layerD layerK layerH; rw [hdata]; exact monomialThreshold_singleton (minAdm M) hpos
  -- and it has a binding axis.
  have hk : ∃ j, (layerK M i₀) j ≠ 0 := by
    show ∃ j, ((routeLayerAtlas M).data i₀).k j ≠ 0
    rw [hdata]; exact foldDivisors_singleton_k_ne_zero (minAdm M)
  have hminR : (1 : ℝ) ≤ (minAdm M : ℝ) := by exact_mod_cast hpos
  have hc'0 : (0 : ℝ) < (c' : ℝ) := by
    have : (0 : ℝ) < (minAdm M : ℝ) / 2 := by linarith
    linarith
  -- `c' ≥ ½·minAdm M = threshold`, so the leaf is at-or-above its threshold.
  have hthr_le :
      monomialThreshold (layerD M i₀) (layerK M i₀) (layerH M i₀) ≤ ENNReal.ofReal (c' : ℝ) := by
    rw [hthr,
      show ((minAdm M : ℝ≥0∞) / 2) = ENNReal.ofReal ((minAdm M : ℝ) / 2) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]]
    exact ENNReal.ofReal_le_ofReal hge
  -- so the achiever leaf's `unitBox` integral diverges.
  have htop : ∫⁻ y in unitBox (layerD M i₀),
      ENNReal.ofReal (monomialIntegrand (layerD M i₀) (layerK M i₀) (layerH M i₀) (c' : ℝ) y) = ⊤ := by
    have hbox := monomialIntegrand_lintegral_box_eq_top' (layerD M i₀) (layerK M i₀) (layerH M i₀)
      hk (c' : ℝ) hthr_le hc'0 (ε := 1) one_pos
    rw [show unitBox (layerD M i₀) = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) from rfl, ← hbox]
    refine setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) ?_
    intro y _
    beta_reduce
    rw [abs_of_nonneg (by unfold monomialIntegrand; positivity : (0 : ℝ) ≤ _)]
  -- a single `⊤` summand forces the whole leaf-sum to `⊤`, contradicting `hsum`.
  have hsum_top : (∑ i : (routeLayerAtlas M).ι, ∫⁻ y in unitBox (layerD M i),
      ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y)) = ⊤ := by
    refine eq_top_mono ?_ rfl
    refine htop ▸ Finset.single_le_sum
      (f := fun i : (routeLayerAtlas M).ι => ∫⁻ y in unitBox (layerD M i),
        ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y))
      (fun i _ => zero_le _) (Finset.mem_univ i₀)
  rw [hsum_top] at hsum
  exact lt_irrefl _ hsum

/-- **The `hfin` atom** (the `cover_le` UPPER leg, the `routeMLayerCover_of_atoms` hypothesis), general
`M`, MODULO the named `RouteMBoxThresholdFinite M`. Below-threshold finiteness: when the layer
leaf-sum is finite at `c'`, the base-nbhd integral `∫⁻_{routeMBaseNbhd M} |routeMCore M|^{−c'}` is
finite. Assembly: `layerCover_leafSum_lt_top_imp_lt_half_minAdm` turns the leaf-sum hypothesis into
`(c':ℝ) < ½·minAdm M`, then the banked `routeMCore_threshold_lt_top_of_box M hbox` (the `c'=0` edge +
the SORRY-FREE `routeMCore_le_matBox` MP box reduction dominated by `hbox`) closes it.

`hbox : RouteMBoxThresholdFinite M` and `hpos : 1 ≤ minAdm M` are EXPLICIT: the layer atlas is
value-only (no chart map to `routeMCore M`), so the leaf-sum supplies only the numerical bound, NOT
the box finiteness — `hbox` is the genuine open analytic input of the upper bound (the same one
`RouteMBoxReduction` names; discharged per-family, e.g. `routeMBoxThresholdFinite_rrp` for `(r,r,p)`).
`hpos` is the non-degeneracy the value lane (`routeLayerAtlas_value`) already carries. -/
theorem routeMLayerCover_hfin (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (hbox : RouteMBoxThresholdFinite M) :
    ∀ c' : NNReal,
      (∑ i : (routeLayerAtlas M).ι, ∫⁻ y in unitBox (layerD M i),
          ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y)) < ⊤ →
      ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) < ⊤ := by
  intro c' hsum
  exact routeMCore_threshold_lt_top_of_box M hbox c'
    (layerCover_leafSum_lt_top_imp_lt_half_minAdm M hpos c' hsum)

end DLNFibre.DLN.RLCT
