import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenDetDecode
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenAnalytic
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenInj
import DLNFibre.DLN.RLCT.Validate.RouteMGenLeafIntegrand

/-!
# `RouteMInteriorLiveGenAtom` — the ASSEMBLED general-`L` LIVE-leaf interior box-divergence ATOM

The general-`L` lift of `RouteMInteriorLiveAtom` (`Fin (2 + 1)`-pinned): the DOWNSTREAM join that
assembles the general-`L` LIVE-leaf ∘ kLDU interior achiever box-divergence from the now-banked "Gen"
pieces (chart / det / leafH / unit / analytic / injectivity / ambient LDU). Layer (c) of the interior
atom — the integration trigger for the R1-LOWER leg.

The pieces (all sorry-free, axiom-clean, banked upstream):

  * chart / pivot / leafH / unit — `RouteMInteriorLiveGenChart` (`interiorLivePhiGen`, `leafPivot`,
    `interiorLive_leafHGen`, `interiorLive_leafHGen_pivot`, `interiorLiveUnitGen`,
    `interiorLiveUnitGen_nonneg`, `routeMCore_interiorLivePhiGen`);
  * det (layer (a)) — `RouteMInteriorLiveGenDetDecode.interiorLive_abs_det'Gen`;
  * analytic leaf facts (layer (b)) — `RouteMInteriorLiveGenAnalytic`
    (`ldu_imageGen` / `ldu_UmeasGen` / `ldu_UboundGen` + the a.e.-positivity `interiorLiveUnit_ae_posGen`,
    and the differentiability `interiorLive_diffGen` via `RouteMInteriorLiveGenHmap`);
  * injectivity — `RouteMInteriorLiveGenInj.interiorLive_injOnGen` (off the domain
    `interiorLiveInjDomGen = {u | u leafPivot ≠ 0 ∧ ∀ j, u j ≠ 0}`);
  * the cov engine — `RouteMNullSliceCov.ldu_cov_of_differentiable_injOn` (M-agnostic, reachable
    transitively via `RouteMInteriorLiveGenAnalytic → …Analytic → …Contract`);
  * the leaf-integrand algebra — `RouteMGenLeafIntegrand.leaf_integrand_of_rate` (M-agnostic).

Deliverables:

  * `interiorLive_covGen` — the general-`L` composite change-of-variables (`ldu_cov_of_differentiable_injOn`
    at the widest extra-axis set `E = univ`, `hdiff := interiorLive_diffGen`, `habsdet :=
    interiorLive_abs_det'Gen`, `hinj := interiorLive_injOnGen` domain-massaged to the engine's set).
  * `interiorLiveNodeChartGen` — the general-`L` `NodeAchieverChart M` bundle (the general-`L` lift of
    `interiorLiveNodeChart`), consuming `hpos : 1 ≤ minAdm M` and `hInt : InteriorDrop M`.
  * `routeMCore_box_diverges_interiorLiveGen` — the general-`L` INTERIOR box-divergence atom
    (`∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`, `c' ≥ ½·minAdm M`, every `ε > 0`), via the M-agnostic
    `routeMCore_box_diverges_of_nodeChart`. This is SHA_int, the R1-LOWER integration trigger.

Axiom profile: the deliverables inherit the pieces' footprint — `[propext, Classical.choice,
Quot.sound]` — S2-FREE since the Stage-A de-cite (the box divergence, formerly via
`monomialIntegrand_lintegral_box_eq_top`, now routes through the proven identity
`monomialThreshold_eq_iInf_axisRatio`, not `monomial_rlct`), NO `sorryAx`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The general-`L` composite change-of-variables -/

/-- **The general-`L` change-of-variables** — assembles the M-agnostic cov engine
`ldu_cov_of_differentiable_injOn` at the widest extra-axis set `E = univ` (all coords nonzero, matching
`interiorLiveInjDomGen`), with `hdiff` (`interiorLive_diffGen`), `habsdet` (`interiorLive_abs_det'Gen`,
layer (a), UNCONDITIONAL — holds ∀u), `hinj` (`interiorLive_injOnGen`, off the domain
`interiorLiveInjDomGen = {u | u leafPivot ≠ 0 ∧ ∀ j, u j ≠ 0}`, massaged to the engine's
`{u | u p ≠ 0 ∧ ∀ j ∈ univ, u j ≠ 0}` via `Set.InjOn.mono`). The general-`L` lift of
`RouteMInteriorLiveAtom.interiorLive_cov`. -/
theorem interiorLive_covGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in interiorLivePhiGen M ha hL h0r h0c ''
        (V \ {x | x (leafPivot M ha hL h0r h0c) = 0}), g x
      = ∫⁻ u in V \ {x | x (leafPivot M ha hL h0r h0c) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (interiorLive_leafHGen M ha hL h0r h0c j))
            * g (interiorLivePhiGen M ha hL h0r h0c u) := by
  -- the engine's injectivity domain (`E = univ`) is a subset of `interiorLiveInjDomGen`
  -- (`∀ j ∈ univ, u j ≠ 0` implies `∀ j, u j ≠ 0`), so `interiorLive_injOnGen` restricts to it.
  have hsub : {u : Fin (routeMAmbient M) → ℝ | u (leafPivot M ha hL h0r h0c) ≠ 0
        ∧ ∀ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))), u j ≠ 0}
      ⊆ interiorLiveInjDomGen M ha hL h0r h0c := by
    rintro u ⟨hup, hall⟩
    exact ⟨hup, fun j => hall j (Finset.mem_univ j)⟩
  have hinj : Set.InjOn (interiorLivePhiGen M ha hL h0r h0c)
      {u : Fin (routeMAmbient M) → ℝ | u (leafPivot M ha hL h0r h0c) ≠ 0
        ∧ ∀ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))), u j ≠ 0} :=
    Set.InjOn.mono hsub (interiorLive_injOnGen M ha hL h0r h0c)
  exact ldu_cov_of_differentiable_injOn (interiorLivePhiGen M ha hL h0r h0c)
    (leafPivot M ha hL h0r h0c) (interiorLive_leafHGen M ha hL h0r h0c)
    (Finset.univ : Finset (Fin (routeMAmbient M)))
    (interiorLive_diffGen M ha hL h0r h0c)
    (fun u => interiorLive_abs_det'Gen M ha hL h0r h0c u) hinj V hV g

/-! ## The general-`L` LIVE-leaf ∘ kLDU interior achiever chart bundle -/

/-- **The general-`L` LIVE-leaf ∘ kLDU interior achiever chart bundle** — `interiorLivePhiGen` with
binding pivot `leafPivot`, the multi-axis `interiorLive_leafHGen`, unit `interiorLiveUnitGen`, and the
LEAF fields wired from the landed general-`L` analytic atoms (`ldu_imageGen` / `ldu_UmeasGen` /
`ldu_UboundGen` + the positivity `interiorLiveUnit_ae_posGen`). The general-`L` lift of
`RouteMInteriorLiveAtom.interiorLiveNodeChart`. -/
noncomputable def interiorLiveNodeChartGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hL : 0 < L) (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (hpos : 1 ≤ minAdm M) (hInt : InteriorDrop M) :
    NodeAchieverChart M where
  hpos := hpos
  phi := interiorLivePhiGen M ha hL h0r h0c
  p := leafPivot M ha hL h0r h0c
  leafH := interiorLive_leafHGen M ha hL h0r h0c
  leafH_pivot := interiorLive_leafHGen_pivot M ha hL h0r h0c
  Ufun := interiorLiveUnitGen M ha hL h0r h0c
  Ubound := ldu_UboundGen M ha hL h0r h0c (interiorLiveUnit_ae_posGen M ha hL h0r h0c hInt)
  Umeas := ldu_UmeasGen M ha hL h0r h0c
  leaf_integrand := fun c =>
    Filter.Eventually.of_forall (fun x =>
      leaf_integrand_of_rate (leafPivot M ha hL h0r h0c) (interiorLive_leafHGen M ha hL h0r h0c)
        (fun y => routeMCore M (interiorLivePhiGen M ha hL h0r h0c y))
        (interiorLiveUnitGen M ha hL h0r h0c)
        (fun y => routeMCore_interiorLivePhiGen M ha hL h0r h0c y)
        (fun y => interiorLiveUnitGen_nonneg M ha hL h0r h0c y) c x)
  cov := interiorLive_covGen M ha hL h0r h0c
  image_subset := ldu_imageGen M ha hL h0r h0c

/-! ## The general-`L` LIVE-leaf ∘ kLDU INTERIOR box-divergence atom (SHA_int) -/

/-- **The general-`L` LIVE-leaf ∘ kLDU INTERIOR box-divergence atom** —
`∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` for `c'` at-or-above `½·minAdm M`, every `ε > 0`, on the
interior class, via the M-agnostic `routeMCore_box_diverges_of_nodeChart` applied to
`interiorLiveNodeChartGen`. The general-`L` lift of
`RouteMInteriorLiveAtom.routeMCore_box_diverges_interiorLive`. This is SHA_int — the `hInterior` atom the
general-`L` R1-LOWER dispatch spine consumes. -/
theorem routeMCore_box_diverges_interiorLiveGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hL : 0 < L) (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (hpos : 1 ≤ minAdm M) (hInt : InteriorDrop M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M
    (interiorLiveNodeChartGen M ha hL h0r h0c hpos hInt) c' hc' ε hε

end DLNFibre.DLN.RLCT
