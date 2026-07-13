import DLNFibre.DLN.RLCT.Validate.HeadlineL1Mint

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.MintRehearsal108` — `#108` mint re-point REHEARSAL (dry-run)

This module is a **rehearsal harness** for the `#108` mint re-point (branch `genm-sj5-mintrehearsal`).
It is NOT wired into the `DLNFibre` aggregator; it exists to green-gate and audit the re-point on a
branch before the real mint (a cherry-pick + one gate) on `(□)`-landing.

The re-point relocates the unsuffixed `aoyagi_learning_coefficient` from `Skeleton` (where it was the
legacy D1▸L2 assembly, 5 `sorryAx`) DOWNSTREAM into `HeadlineL1Mint` (Skeleton cannot import the
prestage — `DeepestBaseL1 → Skeleton` is a cycle), routing it through
`aoyagi_learning_coefficient_prestage`. The legacy assembly survives as
`aoyagi_learning_coefficient_legacy`.

Two things are verified here:

1. **Statement fidelity.** Both the re-homed `aoyagi_learning_coefficient` and the retained
   `aoyagi_learning_coefficient_legacy` inhabit the SAME statement family `AoyagiHeadlineStmt L` — so
   the re-point does not change the headline's type (same `∀ L ≥ 1` conclusion, same `hB/hr/hL/hpos`).
   Both `example`s force elaboration, so this is a genuine defeq check, not an olean-stale one.

2. **Axiom audit (`modulo DecoratedDescent`).** The `#print axioms` lines below show:
   * `aoyagi_learning_coefficient_prestage` — clean-three `[propext, Classical.choice, Quot.sound]`
     (it takes `DecoratedDescent` as a hypothesis, so "modulo `DecoratedDescent`" is exactly this).
     NO `sorryAx`, NO cited-Aoyagi axiom.
   * `aoyagi_learning_coefficient` (re-homed, rehearsal form) — clean-three PLUS `sorryAx`, the single
     `(□)` hole; NO OTHER axiom. So the mint (replace the `sorry` with the proven `DecoratedDescent`
     term) drops exactly `sorryAx` and yields the prestage's clean-three.
   * `aoyagi_learning_coefficient_legacy` — the legacy `sorryAx` profile (the 5 D1▸L2 rungs), for
     contrast.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal

/-- The headline statement family, isolated so the legacy and re-pointed headlines can be checked to
inhabit the identical type (statement fidelity for the `#108` re-point). -/
def AoyagiHeadlineStmt (L : ℕ) : Prop :=
  ∀ (H : Fin (L + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ),
    B.rank = r → (∀ s : Fin (L + 1), r ≤ H s) → 1 ≤ L → (∀ s : Fin (L + 1), r < H s) →
      (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r)

variable {L : ℕ}

/-- Statement fidelity, re-homed side: the re-pointed unsuffixed headline inhabits `AoyagiHeadlineStmt`. -/
example : AoyagiHeadlineStmt L := @aoyagi_learning_coefficient L

/-- Statement fidelity, legacy side: the retained `Skeleton` headline inhabits the SAME family — so the
re-point is type-preserving (same `∀ L ≥ 1` conclusion + `hB/hr/hL/hpos`). -/
example : AoyagiHeadlineStmt L := @aoyagi_learning_coefficient_legacy L

/-! ## Forced axiom audit (`#print axioms` re-elaborates). -/

-- modulo `DecoratedDescent` (taken as hypothesis) — MUST be clean-three, NO `sorryAx`, NO cited-Aoyagi.
#print axioms aoyagi_learning_coefficient_prestage

-- re-homed headline (rehearsal form) — clean-three PLUS the single `(□)` `sorryAx`, NO OTHER axiom.
#print axioms aoyagi_learning_coefficient

-- legacy D1▸L2 assembly — the 5-rung `sorryAx` profile, for contrast.
#print axioms aoyagi_learning_coefficient_legacy

end DLNFibre.DLN.RLCT
