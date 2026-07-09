import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDeepRank0Atom
import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverHfin
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCapB
import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2Build

/-!
# `DLNFibre.DLN.RLCT.Validate.R1ResolutionInterfaceL2` — the R1 resolution interface at `L = 2`

The LAST bounded piece of the L = 2 Aoyagi headline: the route-independent **R1 resolution
interface** at `L = 2` (`R1ResolutionInterface`, `D1ChartProducerL2Build.lean:320`; equivalently the
`hR1_L2` leaf of `HeadlineL2Assembly.lean:87`). For every nondegenerate reduced-width vector
`M : Fin 3 → ℕ` (all layers `> 0`), the deepest DLN core `dlnLoss M 0` at the origin
`(0 : Params M)` has local RLCT `ofReal(lambdaCore M)`.

This is a **wiring** of banked sorry-free pieces — no new deep math. The two genuine
resolution-of-singularities analytic atoms (`hfin` finiteness, `hdiv` box divergence) of the
`IsRouteMCover` assembly are supplied by the banked `L = 2` achiever divergence
(`routeMCore_box_diverges_achiever_L2`) and the depth-2 box finiteness
(`routeMBoxThresholdFinite_mnp`); the value lane (`⨅ monomialThreshold = ofReal(lambdaCore M)`) is
the banked `routeLayerAtlas_value_eq_lambdaCore`; the cover→rlct bridge + the flat↔params transport
are the banked `routeM_rlctAtOn_eq_iInf` / `rlctAtOn_routeMCore_transport`.

## The assembly (all inputs sorry-free)

- **Sub-E** (`one_le_minAdm_of_pos`): `1 ≤ minAdm M` from `∀ s, 0 < M s`, via `minAdm_mnp_eq_inf`
  (every layer-peel stratum value `(m−t)(n−t) + t·p ≥ 1` when `m, n, p ≥ 1`).
- **Sub-A** (the guard-bridge, inline): `(∃ i, monomialThreshold (layerD M i)… ≤ c') →`
  `minAdm M / 2 ≤ c'`, from `iInf_le` + `routeLayerAtlas_value_eq_half_minAdm`.
- **Sub-B** (`hdiv`): the achiever divergence `routeMCore_box_diverges_achiever_L2` through Sub-A.
- **Sub-C** (`hfin`): `routeMLayerCover_hfin M hpos (routeMBoxThresholdFinite_mnp (M 0)(M 1)(M 2))`,
  with the `![M 0, M 1, M 2] = M` funext rewrite.
- **Sub-D** (assemble): `routeMLayerCover_of_atoms` → `IsRouteMCover`; `routeM_rlctAtOn_eq_iInf` +
  `rlctAtOn_routeMCore_transport` → the params-side `⨅`-form; the value lane closes it.

Axioms: `[propext, Classical.choice, Quot.sound]` — S2-FREE since the axiom retirement (2026-07-09;
the box atoms route through the proven identity `monomialThreshold_eq_iInf_axisRatio`), NO `sorryAx`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- **Sub-E — nondegeneracy `⟹ 1 ≤ minAdm`.** For `M : Fin 3 → ℕ` with every layer positive
(`∀ s, 0 < M s`), the minimal admissible codim `minAdm M ≥ 1`. Via `minAdm_mnp_eq_inf` (after the
`![M 0, M 1, M 2] = M` funext): every layer-peel stratum `t ≤ min(M 0)(M 1)` has value
`(M 0 − t)(M 1 − t) + t·(M 2) ≥ 1` — if `t < min(M 0)(M 1)` the product factor is `≥ 1`, and at
`t = min(M 0)(M 1)` the surviving `t·(M 2)` factor is `≥ 1·1 = 1`, since `min(M 0)(M 1) ≥ 1`. -/
theorem one_le_minAdm_of_pos (M : Fin 3 → ℕ) (hMid : ∀ s, 0 < M s) : 1 ≤ minAdm M := by
  have hM : M = (![M 0, M 1, M 2] : Fin 3 → ℕ) := by
    funext s; fin_cases s <;> rfl
  rw [hM, minAdm_mnp_eq_inf]
  have h0 : 0 < M 0 := hMid 0
  have h1 : 0 < M 1 := hMid 1
  have h2 : 0 < M 2 := hMid 2
  refine Finset.le_inf' _ _ (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  -- `t ≤ min (M 0) (M 1)`; show `(M 0 − t)(M 1 − t) + t·(M 2) ≥ 1`.
  rcases Nat.lt_or_ge t (min (M 0) (M 1)) with hlt | hge
  · -- `t < min`, so both factors `> 0`.
    have hf0 : 0 < M 0 - t := by omega
    have hf1 : 0 < M 1 - t := by omega
    have : 1 ≤ (M 0 - t) * (M 1 - t) := Nat.mul_pos hf0 hf1
    omega
  · -- `t = min ≥ 1`, so `t·(M 2) ≥ 1`.
    have htmin : t = min (M 0) (M 1) := by omega
    have htpos : 0 < t := by rw [htmin]; omega
    have : 1 ≤ t * (M 2) := Nat.mul_pos htpos h2
    omega

/-- **The R1 resolution interface at `L = 2`** — the `R1ResolutionInterface`-shaped deliverable.
For every nondegenerate `M : Fin 3 → ℕ` (all layers `> 0`), the deepest DLN core `dlnLoss M 0` at
the origin has local RLCT `ofReal(lambdaCore M)`. Assembled from the banked `L = 2` atoms (achiever
box divergence + the depth-2 box finiteness) through the sorry-free `IsRouteMCover` assembly, the
cover→rlct bridge, the flat↔params transport, and the value lane; no new deep math. -/
theorem r1_resolution_interface_L2 (M : Fin 3 → ℕ) (hMid : ∀ s, 0 < M s) :
    rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last 2))) ℝ) A)
        (fun _ => 0 : Params M)
      = ENNReal.ofReal (lambdaCore M : ℝ) := by
  have hpos : 1 ≤ minAdm M := one_le_minAdm_of_pos M hMid
  -- Sub-C: the finiteness atom `hfin`, from the depth-2 box finiteness (`![M 0, M 1, M 2] = M`).
  have hM : (![M 0, M 1, M 2] : Fin 3 → ℕ) = M := by funext s; fin_cases s <;> rfl
  have hbox : RouteMBoxThresholdFinite M := by
    have := routeMBoxThresholdFinite_mnp (M 0) (M 1) (M 2)
    rwa [hM] at this
  have hfin := routeMLayerCover_hfin M hpos hbox
  -- Sub-A + Sub-B: the box-divergence atom `hdiv`, achiever divergence through the guard-bridge.
  have hdiv : ∀ c' : NNReal,
      (∃ i : (routeLayerAtlas M).ι,
        monomialThreshold (layerD M i) (layerK M i) (layerH M i) ≤ (c' : ℝ≥0∞)) →
      ∀ ε > 0, ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
    intro c' hle ε hε
    obtain ⟨i, hi⟩ := hle
    -- Sub-A: `minAdm M / 2 = ⨅ monomialThreshold ≤ monomialThreshold i ≤ c'`.
    have hguard : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞) := by
      rw [← routeLayerAtlas_value_eq_half_minAdm M hpos]
      exact le_trans (iInf_le _ i) hi
    exact routeMCore_box_diverges_achiever_L2 M hpos c' hguard ε hε
  -- Sub-D: the `IsRouteMCover`, the cover→rlct bridge, the transport, the value lane.
  have hcover := routeMLayerCover_of_atoms M hfin hdiv
  have hbridge := routeM_rlctAtOn_eq_iInf (routeMCore M) (routeMBaseNbhd M)
    (routeLayerAtlas M).ι (layerD M) (layerK M) (layerH M) hcover
  rw [← rlctAtOn_routeMCore_transport M, hbridge, routeLayerAtlas_value_eq_lambdaCore M hpos]

/-- The `L = 2` interface packaged as the `R1ResolutionInterface` predicate (the exact contract
`r1_interface_discharges_degraded` / the `hR1_L2` leaf consume). -/
theorem r1ResolutionInterface_L2 : R1ResolutionInterface :=
  fun M hMid => r1_resolution_interface_L2 M hMid

/-- **The generic-`L` bridge** discharging the `hR1_L2` leaf of `HeadlineL2Assembly`. Under the
headline's `L`-pinning hypotheses (`2 ≤ L`, `L < 3` ⟹ `L = 2`), the interface fires at the
reduced-width vector `M : Fin (L + 1) → ℕ`. `subst`s `L = 2` (so `Fin (L + 1) = Fin 3`,
`Fin.last L = Fin.last 2`) then applies `r1_resolution_interface_L2`. -/
theorem r1_resolution_interface_L2_generic {L : ℕ} (hL2 : 2 ≤ L) (hLlt : L < 3)
    (M : Fin (L + 1) → ℕ) (hMid : ∀ s, 0 < M s) :
    rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A)
        (fun _ => 0 : Params M)
      = ENNReal.ofReal (lambdaCore M : ℝ) := by
  obtain rfl : L = 2 := by omega
  exact r1_resolution_interface_L2 M hMid

end DLNFibre.DLN.RLCT
