import DLNFibre.DLN.RLCT.Validate.HeadlineL1Mint

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineConditionalSpine` — the expedition's durable conditional close-out

The unconditional learning-coefficient headline needs the engine's single remaining geometric hole
`Engine.chartBridgeFaithful_buildTree` (its two open frontiers: the cover `geoAtlasNorm_imageCover`
and the value `LeafPullback`/`leafDiagFrob_geoAtlasNorm`, `GeoAlphaGauge.lean:562`). While that lands
via a focused root-first follow-up, THIS module banks the honestly-clean-three CONDITIONAL result: it
takes the exact statement of `chartBridgeFaithful_buildTree` as an explicit HYPOTHESIS and discharges
the entire chain above the atlas — which is order-independent (navigator-verified) — landing the full
`∀ L ≥ 1` Aoyagi headline `= ofReal (aoyagiLambda H r)` clean-three MODULO that hypothesis.

Why this cannot route through `Engine.engine_box_threshold_finite`: the engine's box-finiteness pulls
its ChartBridge and exponent bounds from `Engine.resolutionOf`, which is *defined* as
`(monomialization_terminates …).choose` — so it BAKES IN the `chartBridge_buildTree` `sorry` through
its definition, and no added hypothesis can remove a `sorry` from a *different* definition's proof
term. So the conditional spine re-derives box-finiteness DIRECTLY over the concrete tree
`buildTree M (conOracle M) conRoot` via `region_glue_of_chartBridge` (clean-three, ChartBridge a
hypothesis) + `minAdm_le_terminalExponents` (clean-three), with the ChartBridge supplied by the
hypothesis' `.toChartBridge` projection — bypassing `resolutionOf`/`monomialization_terminates`/
`engine_box_threshold_finite` entirely.

Discharge (at the follow-up's landing): the hypothesis is `Engine.chartBridgeFaithful_buildTree`
verbatim, so `aoyagi_learning_coefficient_of_chartBridgeFaithful chartBridgeFaithful_buildTree …`
is the unconditional headline, clean-three.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal
open DLNFibre.DLN.RLCT.Engine

variable {L : ℕ}

/-- **The conditional Aoyagi headline — clean-three modulo `chartBridgeFaithful_buildTree`.**
GIVEN the engine's sole remaining geometric obligation `chartBridgeFaithful_buildTree` (as the
explicit hypothesis `hCBF`, its two open frontiers being the cover + the loss-value pullback), the
global learning coefficient (the infimum of the local RLCT over the fibre `mult⁻¹(B)`) of the
`∀ L ≥ 1` deep-linear square-Frobenius loss equals Aoyagi's closed form `aoyagiLambda H r` (`= C/2`),
for every nondegenerate rank-`r` target (`r < H s` at every layer). The `L = 1` arm is the
unconditional regular Morse endpoint `aoyagi_learning_coefficient_L1` (does not use `hCBF`); the
`L ≥ 2` arm feeds `aoyagi_learning_coefficient_gen` a box-finiteness witness rebuilt from `hCBF`
directly over `buildTree M (conOracle M) conRoot` (bypassing `resolutionOf`). Clean-three modulo
`hCBF` — see the module docstring and the `#guard_msgs` gate below. -/
theorem aoyagi_learning_coefficient_of_chartBridgeFaithful
    (hCBF : ∀ (M : Fin (L + 1) → ℕ), 0 < L → (∀ i, 0 < M i) →
      ChartBridgeFaithful M (buildTree M (conOracle M) (conRoot : ConState L)))
    (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  rcases lt_or_ge L 2 with hlt | hge
  · -- `1 ≤ L < 2` ⟹ `L = 1`: the unconditional regular Morse endpoint (`hCBF` unused).
    obtain rfl : L = 1 := by omega
    exact aoyagi_learning_coefficient_L1 H r B hB hr hpos
  · -- `L ≥ 2`: feed `_gen` a box-finiteness witness rebuilt from `hCBF` DIRECTLY over the concrete
    -- tree `buildTree M (conOracle M) conRoot`, bypassing `resolutionOf` (whose def bakes in the
    -- `chartBridge_buildTree` sorry). Mirrors `engine_box_threshold_finite`'s proof, swapping the two
    -- `resolutionOf`-tainted terms for their clean concrete-tree forms.
    have hL0 : 0 < L := by omega
    have hMpos : ∀ i, 0 < (fun s => H s - r) i := fun s => Nat.sub_pos_of_lt (hpos s)
    have hbox : RouteMBoxThresholdFinite (fun s => H s - r) := by
      intro c' hc'
      refine region_glue_of_chartBridge
        (buildTree (fun s => H s - r) (conOracle (fun s => H s - r)) conRoot)
        ((hCBF (fun s => H s - r) hL0 hMpos).toChartBridge) (c' : ℝ) ?_
      intro e he
      have hmin : (minAdm (fun s => H s - r) : ℝ) ≤ (e : ℝ) := by
        exact_mod_cast minAdm_le_terminalExponents (fun s => H s - r) hL0 e he
      have hhalf : (minAdm (fun s => H s - r) : ℝ) / 2 ≤ (e : ℝ) / 2 := by linarith
      exact lt_of_lt_of_le hc' hhalf
    exact aoyagi_learning_coefficient_gen H r B hB hr hL hge hpos hbox

-- Self-contained axiom gate (build FAILS if the footprint drifts): the conditional spine is
-- clean-three MODULO `hCBF`. A `sorryAx` here would mean the proof re-opened a hole (e.g. accidentally
-- routed through `Engine.resolutionOf`, which bakes in the `chartBridge_buildTree` sorry).
/-- info: 'DLNFibre.DLN.RLCT.aoyagi_learning_coefficient_of_chartBridgeFaithful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms aoyagi_learning_coefficient_of_chartBridgeFaithful

end DLNFibre.DLN.RLCT
