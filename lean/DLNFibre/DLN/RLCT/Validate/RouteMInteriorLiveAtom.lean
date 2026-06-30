import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveContract
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveAnalytic
import DLNFibre.DLN.RLCT.Validate.RouteMUPolyLive
import DLNFibre.DLN.RLCT.Validate.RouteMBdetMonomial
import DLNFibre.DLN.RLCT.Validate.RouteMHregPerm

/-!
# `RouteMInteriorLiveAtom` — the assembled LIVE-leaf interior box-divergence ATOM (cov + bundle + atom)

The DOWNSTREAM assembly of the LIVE-leaf ∘ kLDU interior achiever box-divergence. The upstream
`RouteMInteriorLiveContract` builds the chart, the injectivity (`interiorLive_injOn`), the det
(`interiorLive_abs_det`, gated on `interiorLive_BdetMonomial`), the rate, and the unit. The two LEAF-1
analytic facts come from sibling modules that — like this one — sit DOWNSTREAM of the contract (they
reference `interiorLivePhi`/`interiorLiveUnit`), so they CANNOT be wired back into the contract as
one-liners (that would cycle: contract → analytic → contract). This module is the join: it imports the
contract + the two analytic modules and assembles the cov / bundle / atom, wiring

  * `image_subset := ldu_image`            (`RouteMInteriorLiveAnalytic`, genm-ubound, verbatim)
  * `Umeas := ldu_Umeas`                   (`RouteMInteriorLiveAnalytic`, genm-ubound, verbatim)
  * `Ubound := ldu_Ubound … (ae_restrict_of_ae (interiorLiveUnit_ae_pos …))`
        (box bound `ldu_Ubound` + the a.e.-positivity atom `interiorLiveUnit_ae_pos`, genm-upolylive)

The cov consumes the UNCONDITIONAL chart-Jacobian monomial `interiorLive_abs_det'` (proved here: the
contract's gated `interiorLive_BdetMonomial` is replaced by `interiorLive_BdetMonomial_of_hreg`
(`RouteMBdetMonomial`) discharged by `eihd_hreg ha` (`RouteMHregPerm`)). The atom
`routeMCore_box_diverges_interiorLive` is the `hInterior` the dispatch spine consumes; it lives here
(not the contract) so the analytic LEAF-1 facts are visible.

Axiom profile: `routeMCore_box_diverges_interiorLive` depends on exactly
`[propext, Classical.choice, Quot.sound, monomial_rlct]` — the clean-three + the single S2 cited
axiom, NO `sorryAx`. The whole interior leg (monomial fold → `interiorLive_abs_det'` → cov → bundle →
atom) is sorry-free.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin (2 + 1) → ℕ}

/-- **The chart Jacobian is the monomial (UNCONDITIONAL)** — the contract's `interiorLive_abs_det`
re-proved here with the `hreg`-gated `interiorLive_BdetMonomial_of_hreg` discharged by `eihd_hreg ha`
(`RouteMHregPerm`). This is the Route-X join: `RouteMBdetMonomial` (where the monomial fold lives) imports
the contract, so the monomial cannot be wired back into the contract's `interiorLive_BdetMonomial` slot
(that would cycle); instead this DOWNSTREAM module — which imports both `RouteMBdetMonomial` and
`RouteMHregPerm` — closes it and feeds the result to the cov. Verbatim the contract proof, with line 327's
gated `interiorLive_BdetMonomial` replaced by `interiorLive_BdetMonomial_of_hreg … (eihd_hreg ha)`. -/
theorem interiorLive_abs_det' (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (interiorLivePhi ha h0r h0c) u).toLinearMap|
      = ∏ j, |u j| ^ (interiorLive_leafH ha h0r h0c j) := by
  set p₀ := leafPivot M ha (by norm_num) h0r h0c with hp₀
  set B' := fun y => BchartLeaf ha (kLDU M (tach M) ha y) with hB'
  have hmap : interiorLivePhi ha h0r h0c = B' ∘ pivotBlowupOn (activeM M ha) p₀ := by
    funext x
    rw [interiorLivePhi, hmap_leaf ha h0r h0c]
    show BchartLeaf ha (pivotBlowupOn (activeM M ha) p₀ (kLDU M (tach M) ha x)) = _
    rw [interiorLive_commute ha h0r h0c x]; rfl
  have hasDB' : HasFDerivAt B'
      (fderiv ℝ B' (pivotBlowupOn (activeM M ha) p₀ u))
      (pivotBlowupOn (activeM M ha) p₀ u) :=
    ((Bchart_differentiableAt ha _).comp _ (differentiable_kLDU M (tach M) ha _)).hasFDerivAt
  rw [radialComp_abs_det_at M (activeM M ha) p₀ (leafPivot_mem_activeM ha h0r h0c) (activeM_card ha)
    B' (interiorLivePhi ha h0r h0c) u _ hmap hasDB',
    interiorLive_BdetMonomial_of_hreg ha h0r h0c u (eihd_hreg ha)]
  -- |u p₀|^{minAdm−1} · ∏(if j=p₀ then 1 else |u j|^{leafH j}) = ∏ |u j|^{leafH j}
  conv_rhs => rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ p₀)
    (fun j => |u j| ^ (interiorLive_leafH ha h0r h0c j))]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ p₀)
    (fun j => if j = p₀ then (1 : ℝ) else |u j| ^ (interiorLive_leafH ha h0r h0c j))]
  rw [if_pos rfl, one_mul, interiorLive_leafH_pivot ha h0r h0c]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (by simp at hj; exact hj : j ≠ p₀)]

/-- **The change-of-variables** — assembles the cov engine `ldu_cov_of_differentiable_injOn` with
`hdiff` (`interiorLive_diff`), `habsdet` (`interiorLive_abs_det'`, unconditional via `eihd_hreg`),
`hinj` (`interiorLive_injOn`). -/
theorem interiorLive_cov (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in interiorLivePhi ha h0r h0c ''
        (V \ {x | x (leafPivot M ha (by norm_num) h0r h0c) = 0}), g x
      = ∫⁻ u in V \ {x | x (leafPivot M ha (by norm_num) h0r h0c) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (interiorLive_leafH ha h0r h0c j))
            * g (interiorLivePhi ha h0r h0c u) :=
  ldu_cov_of_differentiable_injOn (interiorLivePhi ha h0r h0c)
    (leafPivot M ha (by norm_num) h0r h0c) (interiorLive_leafH ha h0r h0c)
    (interiorLive_E ha h0r h0c) (interiorLive_diff ha h0r h0c)
    (fun u => interiorLive_abs_det' ha h0r h0c u) (interiorLive_injOn ha h0r h0c) V hV g

/-- **The LIVE-leaf ∘ kLDU interior achiever chart bundle** — `interiorLivePhi` with binding pivot
`leafPivot`, the multi-axis `leafH`, unit `interiorLiveUnit`, and the LEAF-1 fields wired from the
landed analytic atoms (`ldu_image`/`ldu_Umeas`/`ldu_Ubound` + the positivity `interiorLiveUnit_ae_pos`). -/
noncomputable def interiorLiveNodeChart (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hpos : 1 ≤ minAdm M) (hInt : InteriorDrop M) :
    NodeAchieverChart M where
  hpos := hpos
  phi := interiorLivePhi ha h0r h0c
  p := leafPivot M ha (by norm_num) h0r h0c
  leafH := interiorLive_leafH ha h0r h0c
  leafH_pivot := interiorLive_leafH_pivot ha h0r h0c
  Ufun := interiorLiveUnit ha h0r h0c
  Ubound := ldu_Ubound ha h0r h0c (interiorLiveUnit_ae_pos ha h0r h0c hInt)
  Umeas := ldu_Umeas ha h0r h0c
  leaf_integrand := fun c =>
    Filter.Eventually.of_forall (fun x =>
      leaf_integrand_of_rate (leafPivot M ha (by norm_num) h0r h0c) (interiorLive_leafH ha h0r h0c)
        (fun y => routeMCore M (interiorLivePhi ha h0r h0c y)) (interiorLiveUnit ha h0r h0c)
        (fun y => routeMCore_interiorLivePhi ha h0r h0c y)
        (fun y => interiorLiveUnit_nonneg ha h0r h0c y) c x)
  cov := interiorLive_cov ha h0r h0c
  image_subset := ldu_image ha h0r h0c

/-- **The LIVE-leaf ∘ kLDU INTERIOR box-divergence atom** —
`∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` for `c'` at-or-above `½·minAdm M`, every `ε > 0`, on the
interior class. The `hInterior` atom the dispatch spine consumes, via the M-agnostic
`routeMCore_box_diverges_of_nodeChart`. -/
theorem routeMCore_box_diverges_interiorLive (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (hpos : 1 ≤ minAdm M) (hInt : InteriorDrop M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M
    (interiorLiveNodeChart ha h0r h0c hpos hInt) c' hc' ε hε

end DLNFibre.DLN.RLCT
