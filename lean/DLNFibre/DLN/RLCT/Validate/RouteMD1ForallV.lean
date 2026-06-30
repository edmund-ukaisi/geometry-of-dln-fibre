import DLNFibre.DLN.RLCT.Validate.D1ChartProducer
import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2
import DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMD1ForallV` — the L = 2 D1 `≥`-leg ∀-`v` slot, as a REDUCTION

The `hD1ge_L2` leaf of `HeadlineL2Assembly` (the L = 2 headline scaffold) is the per-`v`
∀-quantified D1 `≥`-obligation at the front-pivoted `B'`:

    ∀ v ∈ optimalSet H B',
      rlctAt H (dlnLoss H B') (deepestPoint H r B' …) ≤ rlctAt H (dlnLoss H B') v.

## STEP-0 finding (the honest scope — a GENUINE square-widths obstruction at general `H`)

Read against the banked pieces (decorrelated Codex xhigh, 2026-06-30), the leaf at GENERAL `H`
(reduced widths `H − r` possibly RECTANGULAR) is NOT closable through the banked square-only D1
engine. The structural facts:

  * The underlying per-`v` producer `deepest_le_of_optimal_chart` (`D1ChartProducer`) is GENERAL: at
    any optimal `v` it reduces the per-`v` `≥` to EXACTLY three obligations —
      (i)  the deepest-side `#44` equality `hDeepest : rlctAt deepest = nReg/2 + coreDeepest`,
      (ii) the IFT chart-producer inputs at `v` (the post-chart sum-of-squares form `F = ∑ s² + Q`,
           the slice residual `R = Q(0,·)`, measurability, the quasi-split comparison `hcmp`), and
      (iii) `hCore : coreDeepest ≤ rlctAtOn R t0` (the value-level slice-residual ≥ deepest-core
           comparison).
  * Obligation (i) IS producible at the front-pivot `B'`, sorry-free, for the RECTANGULAR core
    `coreDeepest = ofReal(lambdaCore (H − r))`, via `deepest_regular_core_normal_form_L2_front`
    (#44-at-L2, `hJfront`-free) fed the R1 interface value at `M = H − r`.
  * Obligations (ii)+(iii) at a GENERAL optimal `v` are the genuinely-Mathlib-lacking analytic
    content (the constant-`nReg` IFT chart at general `v` + the value-level core comparison). The
    `D1ChartProducer` docstring surfaces (iii) explicitly as the open "kill residual" gap: at a
    MIDDLE-STRATUM `v` the deepest-type germ factorization `hRform` is FALSE, and `hCore` survives
    only at the VALUE level. The banked square-only engine route (`rlctAt_deepest_le_of_optimal_L2`
    via the second peel) discharges (iii) ONLY when the deepest reduced widths are SQUARE `(m,m,m)`
    (the `coreDeepest = ofReal(lambdaCore (squareWidths m))` scope, a 164-strata sweep `1 ≤ m ≤ 8`),
    so it CANNOT match the rectangular `#44` value `ofReal(lambdaCore (H − r))` for non-square
    `H − r`.

So the ∀-`v` leaf at general `H` is gated on the per-`v` chart-producer obligation (ii)+(iii) at a
general optimal `v`, which is NOT banked sorry-free by any route. This module does NOT force a
vacuous proof and introduces NO `sorry` / `axiom`. It delivers the sorry-free REDUCTION that
exposes EXACTLY that single open obligation, plus the #44 production from R1, so the leaf becomes a
one-liner the day the general-`v` chart producer lands.

## What this module delivers (the bedrock)

  * `D1PerVChartObligation H r B' v` — the per-`v` chart-producer obligation, a `Prop` bundling the
    genuinely-unbuilt analytic content (a slice type `Y`, the producer's chart inputs at `v` with
    `m = nRegL2 H r`, AND the value-level `hCore` for `coreDeepest = ofReal(lambdaCore (H − r))`).
    This is the precise residual debt — name = content.
  * `d1ge_perV_of_obligation` — at the front-pivot `B'`, GIVEN the R1 interface value at `H − r`
    (the same `R1ResolutionInterface`-shape the scaffold's `hR1_L2` leaf supplies) AND the per-`v`
    obligation, the per-`v` `≥` holds. Proof: produce `hDeepest` (#44) from R1 via
    `deepest_regular_core_normal_form_L2_front`, then call `deepest_le_of_optimal_chart`.
  * `hD1ge_L2_of_obligations` — the ∀-`v` leaf, EXACTLY matching `hD1ge_L2`, reduced to (R1 at
    `H − r`) + (∀ `v ∈ optimalSet`, the per-`v` obligation). A direct `exact` discharges `hD1ge_L2`
    once those two land (R1 is the scaffold's other leaf; the per-`v` obligation is the open D1
    analytic content).

Scope L = 2 only (`hL2 : 2 ≤ L`, `hLlt : L < 3`); the general-L arm stays the named wall #120. This
module does NOT edit `HeadlineL2Assembly` (single-writer) nor the R1-interior files.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The per-`v` D1 chart-producer obligation at L = 2 (the genuinely-unbuilt analytic content).**
At an optimal `v ∈ optimalSet H B`, the obligation asserts the existence of the constant-`nReg` IFT
chart producer's inputs (slice type `Y`, post-chart sum-of-squares form `F = ∑ s² + Q` with
`m = nRegL2 H r`, slice residual `R = Q(0,·)`, measurability, the quasi-split comparison `hcmp`)
PLUS the value-level core comparison `hCore : ofReal(lambdaCore (H − r)) ≤ rlctAtOn R t0`. This is
EXACTLY the input `deepest_le_of_optimal_chart` consumes (minus `hDeepest`, produced here from R1).
It is the precise residual debt of the D1 `≥`-leg at general `v` — the chart at general `v` + the
value-level
`hCore` (the surfaced "kill residual" gap), which Mathlib v4.29 lacks (no Morse / constant-rank
quadratic split) and no banked route discharges sorry-free at general (rectangular) `H − r`. -/
def D1PerVChartObligation (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H) : Prop :=
  ∃ (Y : Type) (_ : PseudoMetricSpace Y) (_ : MeasureSpace Y) (_ : ProperSpace Y)
      (_ : IsFiniteMeasureOnCompacts (volume : Measure Y)) (_ : BorelSpace Y)
      (F : (Fin (nRegL2 H r) → ℝ) × Y → ℝ) (Q : (Fin (nRegL2 H r) → ℝ) × Y → ℝ)
      (R : Y → ℝ) (t0 : Y),
    rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin (nRegL2 H r) → ℝ), t0) ∧
    (∀ p, F p = (∑ i, p.1 i ^ 2) + Q p) ∧
    (∀ p, 0 ≤ Q p) ∧
    Measurable F ∧
    (∀ t, R t = Q (0, t)) ∧
    Measurable R ∧
    (∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0) ∧
    (∃ C : ℝ, 0 < C ∧
      ∃ U ∈ 𝓝 ((0 : Fin (nRegL2 H r) → ℝ), t0), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p) ∧
    ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) ≤ rlctAtOn R t0

/-- **The per-`v` D1 `≥` at the front-pivot `B`, from R1 + the chart obligation (L = 2).** Given the
front-pivot full-rank data (`htop`/`hcolfront`, the headline-WLOG facts), the R1 interface value at
the reduced widths `M = H − r` (`hRValue`), and the per-`v` chart obligation at an optimal `v`, the
deepest point has `≤` local RLCT than `v`. Proof: `deepest_regular_core_normal_form_L2_front` turns
R1 into the `#44` equality `hDeepest` for the RECTANGULAR core `ofReal(lambdaCore (H − r))`; then
`deepest_le_of_optimal_chart` consumes the obligation's chart inputs + the value-level `hCore`. -/
theorem d1ge_perV_of_obligation (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (2 + 1), r ≤ H s) (hL : 1 ≤ 2) (hL2 : 2 ≤ 2) (hLlt : 2 < 3)
    (hpos : ∀ s : Fin (2 + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last 2)) → Fin (H (Fin.last 2)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last 2)) : Fin r → Fin (H (Fin.last 2)))).rank = r)
    (hRValue :
      rlctAtOn
          (fun A : Params (fun s => H s - r) =>
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ) A)
          (fun _ => 0 : Params (fun s => H s - r))
        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (v : Params H) (hObl : D1PerVChartObligation H r B v) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v := by
  -- #44-at-L2: the deepest-side equality for the RECTANGULAR reduced core.
  have hDeepest := deepest_regular_core_normal_form_L2_front H r B hB hr hL hL2 hpos
    htop hcolfront hLlt hRValue
  -- unpack the per-`v` chart-producer obligation at this `v`.
  obtain ⟨Y, _, _, _, _, _, F, Q, R, t0, hchart, hF, hQ0, hFmeas, hR, hRmeas, hRne,
      ⟨C, hC, hcmp⟩, hCore⟩ := hObl
  -- the producer consumes `m = nRegL2 H r` and `coreDeepest = ofReal(lambdaCore (H − r))`.
  exact deepest_le_of_optimal_chart H r B (deepestPoint H r B hB hr hL) v F Q R t0
    (ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) hDeepest hchart hF hQ0 hFmeas hR hRmeas
    hRne C hC hcmp hCore

/-- **The `hD1ge_L2` leaf, reduced to (R1 at `H − r`) + (∀-`v` chart obligation).** EXACTLY the
`HeadlineL2Assembly` leaf (stated at `L = 2`): the ∀-`v` D1 `≥`-leg at the front-pivot `B'` (here
`B`), with the front-pivot full-rank WLOG facts. Reduced to the two precise residual debts:
  * `hRValue` — the R1 interface value at the reduced widths `H − r` (the same value the scaffold's
    separate `hR1_L2` leaf supplies, specialized at `M = H − r`);
  * `hObl` — for EVERY optimal `v`, the per-`v` chart-producer obligation (the genuinely-unbuilt
    general-`v` IFT chart + value-level `hCore`, the surfaced D1 "kill residual" gap).
The hypotheses `htop`/`hcolfront` are the headline-WLOG facts `hB'_top`/`hB'_colfront` from
`headline_frontRowColPivot_exists`. The scaffold wires this by `obtain rfl : L = 2 := by omega` then
a direct `exact` once both residual debts land. -/
theorem hD1ge_L2_of_obligations (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (2 + 1), r ≤ H s) (hL : 1 ≤ 2) (hL2 : 2 ≤ 2) (hLlt : 2 < 3)
    (hpos : ∀ s : Fin (2 + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last 2)) → Fin (H (Fin.last 2)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last 2)) : Fin r → Fin (H (Fin.last 2)))).rank = r)
    (hRValue :
      rlctAtOn
          (fun A : Params (fun s => H s - r) =>
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ) A)
          (fun _ => 0 : Params (fun s => H s - r))
        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (hObl : ∀ v ∈ optimalSet H B, D1PerVChartObligation H r B v) :
    ∀ v ∈ optimalSet H B,
      rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v := by
  intro v hv
  exact d1ge_perV_of_obligation H r B hB hr hL hL2 hLlt hpos htop hcolfront hRValue v (hObl v hv)

end DLNFibre.DLN.RLCT
