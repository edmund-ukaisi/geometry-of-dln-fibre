import DLNFibre.DLN.RLCT.Validate.RouteMAchieverFullHNoFree
import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverHfin
import DLNFibre.DLN.RLCT.Validate.RouteMLayerValue
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanChart

/-!
# `DLNFibre.DLN.RLCT.Validate.R1ResolutionGeneral` — the R1 resolution interface at general `L`

The general-`L` mirror of `R1ResolutionInterfaceL2` (`r1_resolution_interface_L2`). For a
nondegenerate reduced-width vector `M : Fin (L + 1) → ℕ` (all layers `> 0`) and the **named
box-finiteness** analytic input (`hbox : RouteMBoxThresholdFinite M`), the deepest DLN core
`dlnLoss M 0` at the origin `(0 : Params M)` has local RLCT `ofReal(lambdaCore M)`.

This is a **wiring** of banked ∀L pieces, swapping the L = 2 achiever
(`routeMCore_box_diverges_achiever_L2`) for the general-`L` `hNo`-FREE achiever
(`routeMCore_box_diverges_achiever_full'`, `RouteMAchieverFullHNoFree.lean`).

## `hNo` is DROPPED (de-conditionalized)

The achiever's `NoInteriorBothDrop` obligation is now discharged inside
`routeMCore_box_diverges_achiever_full'` by the `InteriorDrop`/`¬InteriorDrop` case split (the
interior branch is unconditional; the `¬InteriorDrop` branch obtains `hNo` from
`noInteriorBothDrop_of_not_interiorDrop`, which needs only `0 < Wext M L = M (Fin.last L)`,
positive by `hMid`). So `hNo` is no longer a hypothesis of `r1_resolution_general`.

## One genuine hypothesis that is NOT ∀L-dischargeable (precision discipline)

* **`hbox : RouteMBoxThresholdFinite M`** — the box-finiteness for the `hfin` (finiteness) leg.
  `routeMLayerCover_hfin` is ∀L in its signature but requires this named analytic input, which is
  discharged **only** for the depth-2 `(m,n,p)` / `(r,r,p)` families
  (`routeMBoxThresholdFinite_mnp` / `_rrp`); for general/deeper `M` it is the documented open gap
  (`RouteMBoxReduction.lean`: "for general `M` there is no literal ∀M wiring — a category error").
  Carried here as an explicit hypothesis, next to the claim.

## The assembly (all inputs sorry-free)

- **Sub-E** (`one_le_minAdm_of_pos_general`): `1 ≤ minAdm M` from `∀ s, 0 < M s` (for `1 ≤ L`), via
  the layer-peeling recursion `minAdmRec` (`minAdmRec_eq_minAdm`) and the all-positive-strata
  induction.
- **Sub-F** (`deepestCoords_nonempty_of_pos`): `∀ hL, (deepestCoords M hL).Nonempty` from `hMpos`,
  via `deepestCoords_card = M (deepLayer).castSucc · M (deepLayer).succ > 0`.
- **Sub-A** (the guard-bridge, inline): `(∃ i, monomialThreshold (layer i) ≤ c') → ½·minAdm M ≤ c'`,
  from `iInf_le` + `routeLayerAtlas_value_eq_half_minAdm`.
- **Sub-B** (`hdiv`): the general `hNo`-free achiever `routeMCore_box_diverges_achiever_full'`
  through Sub-A, supplied `hMpos`/`hne` (no `hNo`).
- **Sub-C** (`hfin`): `routeMLayerCover_hfin M hpos hbox`.
- **Sub-D** (assemble): `routeMLayerCover_of_atoms` → `IsRouteMCover`; `routeM_rlctAtOn_eq_iInf` +
  `rlctAtOn_routeMCore_transport` → the params-side `⨅`-form; the value lane closes it.

Axioms: exactly `[propext, Classical.choice, Quot.sound]` — S2-FREE since the Stage-A de-cite (the
value lane routes through the proven identity `monomialThreshold_eq_iInf_axisRatio`, not
`monomial_rlct`; verified AxCheck:349), no `sorryAx`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **Sub-E — nondegeneracy `⟹ 1 ≤ minAdm`, general `L ≥ 1`.** For `M : Fin (L + 1) → ℕ` with
every layer positive and at least one genuine layer (`1 ≤ L`), `minAdm M ≥ 1`. Proved on the
layer-peeling recursion `minAdmRec` (`minAdmRec_eq_minAdm`): a leaf (`L = 1`) has value
`M 0 · M 1 ≥ 1`; a `≥ 3`-width chain has every stratum value
`(M0−t)(M1−t) + minAdmRec(redChain t M)` at least `1` — if `t < min(M0,M1)` the product factor is
`≥ 1`, and at `t = min(M0,M1) ≥ 1` the reduced chain `(t, M2, …, M_L)` is all-positive, so the
recursive value is `≥ 1` by the inner induction. -/
theorem one_le_minAdmRec_of_pos :
    ∀ {L : ℕ}, 1 ≤ L → ∀ M : Fin (L + 1) → ℕ, (∀ s, 0 < M s) → 1 ≤ minAdmRec M
  | 0, hL, _, _ => by omega
  | 1, _, M, hMpos => by
      rw [minAdmRec_leaf]; exact Nat.mul_pos (hMpos 0) (hMpos 1)
  | (k + 1 + 1), _, M, hMpos => by
      rw [minAdmRec_succ_succ]
      refine Finset.le_inf' _ _ (fun t ht => ?_)
      rw [Finset.mem_range] at ht
      -- `t ≤ min (M 0) (M 1)`; show `(M0−t)(M1−t) + minAdmRec(redChain t M) ≥ 1`.
      rcases Nat.lt_or_ge t (min (M 0) (M 1)) with hlt | hge
      · -- `t < min`, so both factors `> 0`.
        have hf0 : 0 < M 0 - t := by omega
        have hf1 : 0 < M 1 - t := by omega
        have : 1 ≤ (M 0 - t) * (M 1 - t) := Nat.mul_pos hf0 hf1
        omega
      · -- `t = min ≥ 1`; the reduced chain `(t, M2, …, M_L)` is all-positive.
        have htmin : t = min (M 0) (M 1) := by omega
        have htpos : 0 < t := by rw [htmin]; simp only [lt_min_iff]; exact ⟨hMpos 0, hMpos 1⟩
        have hredpos : ∀ s, 0 < redChain t M s := by
          intro s
          refine Fin.cases ?_ (fun i => ?_) s
          · rw [redChain_zero]; exact htpos
          · rw [redChain_succ]; exact hMpos _
        have hrec : 1 ≤ minAdmRec (redChain t M) :=
          one_le_minAdmRec_of_pos (by omega) (redChain t M) hredpos
        omega

/-- **Sub-E packaged for `minAdm`.** `1 ≤ minAdm M` from `∀ s, 0 < M s` and `1 ≤ L`. -/
theorem one_le_minAdm_of_pos_general (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L)
    (hMpos : ∀ s, 0 < M s) : 1 ≤ minAdm M := by
  rw [← minAdmRec_eq_minAdm]
  exact one_le_minAdmRec_of_pos hL M hMpos

/-- **Sub-F — the deepest block is nonempty at every positive `L`.** From all-positive widths
(`hMpos`), `(deepestCoords M hL).card = M (deepLayer).castSucc · M (deepLayer).succ > 0`, so the
deepest coordinate block is nonempty. Supplies the achiever's `hne`. -/
theorem deepestCoords_nonempty_of_pos (M : Fin (L + 1) → ℕ) (hMpos : ∀ s, 0 < M s) :
    ∀ hL : 0 < L, (deepestCoords M hL).Nonempty := by
  intro hL
  rw [← Finset.card_pos, deepestCoords_card M hL]
  exact Nat.mul_pos (hMpos _) (hMpos _)

/-- **The R1 resolution interface at general `L`** — the general-`L` mirror of
`r1_resolution_interface_L2`. For every nondegenerate `M : Fin (L + 1) → ℕ` (all layers `> 0`, at
least one genuine layer `1 ≤ L`) and the named box-finiteness input (`hbox`), the deepest DLN core
`dlnLoss M 0` at the origin has local RLCT `ofReal(lambdaCore M)`. Assembled from the general-`L`
`hNo`-free achiever box divergence (`routeMCore_box_diverges_achiever_full'`) through the sorry-free
`IsRouteMCover` assembly, the cover→rlct bridge, the flat↔params transport, and the value lane.
Conditional ONLY on `hbox` (the open box-finiteness); `hNo` is discharged inside the achiever via the
`InteriorDrop`/bridge case split. -/
theorem r1_resolution_general (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (hMid : ∀ s, 0 < M s)
    (hbox : RouteMBoxThresholdFinite M) :
    rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A)
        (fun _ => 0 : Params M)
      = ENNReal.ofReal (lambdaCore M : ℝ) := by
  have hpos : 1 ≤ minAdm M := one_le_minAdm_of_pos_general M hL hMid
  have hne : ∀ hL : 0 < L, (deepestCoords M hL).Nonempty :=
    deepestCoords_nonempty_of_pos M hMid
  -- Sub-C: the finiteness atom `hfin`, from the named box-finiteness `hbox`.
  have hfin := routeMLayerCover_hfin M hpos hbox
  -- Sub-A + Sub-B: the box-divergence atom `hdiv`, general achiever through the guard-bridge.
  have hdiv : ∀ c' : NNReal,
      (∃ i : (routeLayerAtlas M).ι,
        monomialThreshold (layerD M i) (layerK M i) (layerH M i) ≤ (c' : ℝ≥0∞)) →
      ∀ ε > 0, ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
    intro c' hle ε hε
    obtain ⟨i, hi⟩ := hle
    -- Sub-A: `½·minAdm M = ⨅ monomialThreshold ≤ monomialThreshold i ≤ c'`.
    have hguard : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞) := by
      rw [← routeLayerAtlas_value_eq_half_minAdm M hpos]
      exact le_trans (iInf_le _ i) hi
    exact routeMCore_box_diverges_achiever_full' M hpos hMid hne c' hguard ε hε
  -- Sub-D: the `IsRouteMCover`, the cover→rlct bridge, the transport, the value lane.
  have hcover := routeMLayerCover_of_atoms M hfin hdiv
  have hbridge := routeM_rlctAtOn_eq_iInf (routeMCore M) (routeMBaseNbhd M)
    (routeLayerAtlas M).ι (layerD M) (layerK M) (layerH M) hcover
  rw [← rlctAtOn_routeMCore_transport M, hbridge, routeLayerAtlas_value_eq_lambdaCore M hpos]

end DLNFibre.DLN.RLCT
