import DLNFibre.DLN.RLCT.Engine.EngineObligations
import DLNFibre.DLN.RLCT.Validate.HeadlineGenAssembly

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineDriver` — the engine's top-level composition

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.** The driver of the transform-only Aoyagi engine: it composes the `Engine.EngineObligations`
holes into the single Prop the engine owes upstream, `∀ M, RouteMBoxThresholdFinite M` (the map's
`hbox-root`, `Validate/RouteMBoxReduction.lean` — consumed here **verbatim**, anchor-pin
discipline). The composition is `sorry`-free *itself*: every hole lives in a named obligation, and
the kernel checks they fit into the headline.

**Layer-B fence (compass, convening #1), verbatim: "A Layer-B lemma that integrates anything is
off-contract."** Accordingly the only integral-valued obligation in the chain is the assembly
`region_glue`; `reduction_layer`/`case_step_invariant`/`monomialization_terminates`/
`exponent_ledger_bridge` are structural. The wiring:

1. `region_glue` (ASSEMBLY) makes the box integral finite once `c'` is below every terminal ratio,
   given `coverage_theorem`;
2. `exponent_ledger_bridge` turns the `c' < ½·minAdm M` hypothesis into `c' < ½·e` for every
   terminal exponent `e` (`minAdm M ≤ e`), discharging `region_glue`'s ratio side-condition.

`reduction_layer` (the regular peel, structural) and `case_step_invariant` set up and validate the
`resolutionOf M` that `coverage_theorem`/`region_glue` consume; the non-deepest reduction is
theorem4-localization's (coverage-design's node) — kept off the driver's chain to keep it acyclic.

The closing `example` witnesses the *fit*: the driver's output plugs into the `hbox` slot of the
banked `aoyagi_learning_coefficient_gen` (`Validate/HeadlineGenAssembly.lean`), so completing the
obligations unconditionalises the learning-coefficient headline.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped ENNReal

variable {L : ℕ}

/-- **The engine driver** (map: `hbox-root`, discharged by `engine-route`). For every width vector
`M`, the layer-product box integral is finite below the geometric threshold `½·minAdm M` — i.e.
`RouteMBoxThresholdFinite M`, the sole Prop the engine owes. A `@[blueprint]` composition of the
`EngineObligations` holes; `sorry`-free itself (the holes are the obligations). -/
@[blueprint] theorem engine_box_threshold_finite (M : Fin (L + 1) → ℕ) :
    RouteMBoxThresholdFinite M := by
  intro c' hc'
  -- assembly (region_glue): the box integral is finite once `c'` is below every terminal ratio
  refine region_glue M (coverage_theorem M) (c' : ℝ) ?_
  intro e he
  -- ledger bridge: `minAdm M ≤ e`, and `c' < ½·minAdm M`, so `c' < ½·e`
  have hmin : (minAdm M : ℝ) ≤ (e : ℝ) := by exact_mod_cast (exponent_ledger_bridge M).1 e he
  have hhalf : (minAdm M : ℝ) / 2 ≤ (e : ℝ) / 2 := by linarith
  exact lt_of_lt_of_le hc' hhalf

/-- **Fit witness.** The driver's output is exactly the `hbox` the banked general headline needs:
plugging `engine_box_threshold_finite (fun s => H s − r)` into `aoyagi_learning_coefficient_gen`'s
`hbox` slot yields the learning-coefficient identity with no carried Aoyagi hypothesis. This is the
`discharges` edge `engine-route → hbox-root → mint-repoint`, kernel-checked. -/
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) :=
  aoyagi_learning_coefficient_gen H r B hB hr hL hL2 hpos
    (engine_box_threshold_finite (fun s => H s - r))

end DLNFibre.DLN.RLCT.Engine
