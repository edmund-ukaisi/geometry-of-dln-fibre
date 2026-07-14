import DLNFibre.DLN.RLCT.Validate.HeadlineGenAssembly
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec

/-!
# `#108` mint pre-stage — the fully-general headline, unconditional MODULO `DecoratedDescent`

This module pre-stages the final `aoyagi_learning_coefficient` mint (operator directive 2026-07-13:
"pre-stage the #108 mint wiring against the conditional headline"). It verifies, NOW, that the
composition

  `DecoratedDescent`  --(driver)-->  `(□) ∀M`  --(hbox slot)-->  unconditional `aoyagi_learning_coefficient_gen`

typechecks end-to-end, so that when the sole remaining analytic contract `DecoratedDescent` is proven
(from `DecoratedStepHyp` + `DecoratedBaseHyp` + the trivial-admissibility witness), minting the
unconditional fully-general Aoyagi learning coefficient is the single application below — no wiring
surprises at the finish.

**What is discharged vs assumed.** `aoyagi_learning_coefficient_gen` (`HeadlineGenAssembly`) is the honest
fully-general result, conditional ONLY on `hbox = RouteMBoxThresholdFinite (H − r)`. The driver
`routeMBoxThresholdFinite_of_decoratedDescent` (`RouteMSJDecoratedRec`, clean-three) turns
`DecoratedDescent` into `(□) ∀M`, so this lemma is unconditional GIVEN `DecoratedDescent`. At mint time
(`#108`) the `hDescent` hypothesis is supplied by the proven descent and dropped; the unsuffixed
`aoyagi_learning_coefficient` (currently routed through the old sorry-carrying L2 skeleton) is re-pointed
onto this general result. The `L = 1` endpoint (this lemma carries `hL2 : 2 ≤ L`, matching `_gen`) is a
separate unconditional path folded in at mint time.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal Topology

variable {L : ℕ}

/-- **`#108` mint pre-stage — the general headline, unconditional modulo `DecoratedDescent`.** Given
the sole remaining analytic contract `DecoratedDescent`, the global learning coefficient (the infimum
of the local RLCT over the optimal set / fibre) equals Aoyagi's closed form `aoyagiLambda H r`, for every
nondegenerate DLN target (`r < H s` at every layer, `2 ≤ L`). The `(□)` box-finiteness that
`aoyagi_learning_coefficient_gen` needs is discharged by the decorated-recursion driver from
`hDescent`. Minting `#108` = supply the proof of `DecoratedDescent` here. -/
theorem aoyagi_learning_coefficient_gen_of_descent
    (hDescent : DecoratedDescent)
    (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) :=
  aoyagi_learning_coefficient_gen H r B hB hr hL hL2 hpos
    (routeMBoxThresholdFinite_of_decoratedDescent hDescent L (fun s => H s - r))

end DLNFibre.DLN.RLCT
