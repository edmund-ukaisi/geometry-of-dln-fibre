import DLNFibre.DLN.RLCT.Validate.DeepestBaseL1
import DLNFibre.DLN.RLCT.Engine.EngineDriver

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineL1Mint` — the `L = 1` headline endpoint + the `#108` case-split

Two deliverables for the fully-general (`∀ L ≥ 1`) Aoyagi headline:

* **`aoyagi_learning_coefficient_L1`** — the `L = 1` (single-layer) case, UNCONDITIONAL and sorry-free.
  At one layer `prod H A = A 0` (`prod_L1`), so `dlnLoss H B` is the full nondegenerate square-Frobenius
  norm `‖A 0 − B‖²`; the fibre `optimalSet H B = {A | A 0 = B}` is the singleton `{deepestPoint}` (D1 is
  trivial — no other fibre point), and the local RLCT at that point is `H⁰·H¹/2 = aoyagiLambda H r`
  (banked regular-block RLCT `deepest_regular_core_normal_form_L1` + the arithmetic fold
  `reg_shift_add_core_eq_aoyagiLambda`). This is the regular Morse endpoint that the general descent
  (`aoyagi_learning_coefficient_gen`, `hL2 : 2 ≤ L`) cannot reach.

* **`aoyagi_learning_coefficient_prestage`** — the `∀ L ≥ 1` wrapper, pre-staged ON THIS BRANCH (the
  canonical unsuffixed `aoyagi_learning_coefficient` at `Skeleton.lean:1680` still routes through the
  old sorry-carrying L2 skeleton; this is its eventual replacement, flagged for the controller to
  re-point at mint). It case-splits `L = 1 → aoyagi_learning_coefficient_L1` / `2 ≤ L →
  aoyagi_learning_coefficient_gen` fed the ENGINE box-finiteness witness
  `Engine.engine_box_threshold_finite (H − r)` (the direct engine composition — the
  `EngineDriver` fit shape). There is NO `DecoratedDescent`/`hDescent` hypothesis: the `(□)`
  box-finiteness discharge is now the engine's own, so the `L ≥ 2` arm carries a `sorryAx` THROUGH
  `engine_box_threshold_finite` (the engine's SINGLE open hole) until that flips clean-three — at
  which point `aoyagi_learning_coefficient_prestage` flips clean-three automatically. Everything else
  is sorry-free.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal

variable {L : ℕ}

/-- **The `L = 1` (single-layer) Aoyagi headline endpoint — unconditional, sorry-free.** For a
single-layer chain the multiplication map is the identity `prod H A = A 0`, so `dlnLoss H B` is the
full nondegenerate square-Frobenius norm and the fibre `optimalSet H B` is the singleton
`{deepestPoint}`. The global learning coefficient (infimum of the local RLCT over the fibre) is the
regular full-dimension value `H⁰·H¹/2 = aoyagiLambda H r`. The all-widths-positive requirement (else
the loss is an empty sum and `rlctAt = ⊤`) is supplied by `hpos`. -/
theorem aoyagi_learning_coefficient_L1 (H : Fin (1 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 1))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (1 + 1), r ≤ H s) (hpos : ∀ s : Fin (1 + 1), r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  have hL : (1 : ℕ) ≤ 1 := le_refl 1
  have hH0 : 0 < H 0 := Nat.lt_of_le_of_lt (Nat.zero_le r) (hpos 0)
  have hH1 : 0 < H (Fin.last 1) := Nat.lt_of_le_of_lt (Nat.zero_le r) (hpos (Fin.last 1))
  have hdp0 : prod H (deepestPoint H r B hB hr hL) = B := (deepestPoint_isDeep H r B hB hr hL).1
  -- the fibre is the singleton {deepestPoint}: `A 0 = B` fixes `A` (Fin 1 → matrix)
  have hset : optimalSet H B = {deepestPoint H r B hB hr hL} := by
    ext A
    simp only [optimalSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hA
      funext s
      rw [Subsingleton.elim s 0]
      have hA0 : A 0 = B := by rw [← prod_L1 H A]; exact hA
      have hd0 : deepestPoint H r B hB hr hL 0 = B := by
        rw [← prod_L1 H (deepestPoint H r B hB hr hL)]; exact hdp0
      rw [hA0, hd0]
    · intro hA; rw [hA]; exact hdp0
  rw [hset]
  -- infimum over a singleton = the value at that point
  have hsingle : (⨅ w ∈ ({deepestPoint H r B hB hr hL} : Set (Params H)),
        rlctAt H (dlnLoss H B) w) = rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) :=
    le_antisymm (iInf₂_le _ (Set.mem_singleton _))
      (le_iInf₂ (fun w hw => by rw [Set.mem_singleton_iff] at hw; rw [hw]))
  rw [hsingle, deepest_regular_core_normal_form_L1 H r B hB hr hH0 hH1,
    reg_shift_add_core_eq_aoyagiLambda H r hr hL]

/-- **`#108` mint pre-stage — the `∀ L ≥ 1` headline via the `L = 1` / `L ≥ 2` case-split.** The
`L = 1` arm is `aoyagi_learning_coefficient_L1` (regular Morse endpoint, sorry-free); the `L ≥ 2` arm
is `aoyagi_learning_coefficient_gen` fed the engine box-finiteness witness
`Engine.engine_box_threshold_finite (H − r)` — the DIRECT engine composition (the `EngineDriver` fit
shape), with NO `DecoratedDescent` hypothesis. The `(□)` box-finiteness discharge is the engine's
own, so this wrapper carries a `sorryAx` THROUGH `engine_box_threshold_finite` (the engine's single
open hole) and flips clean-three the instant that hole lands. This is the eventual replacement of the
canonical `aoyagi_learning_coefficient` (`Skeleton.lean:1680`, still on the old sorry L2 skeleton) —
controller re-points at mint. -/
theorem aoyagi_learning_coefficient_prestage
    (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  rcases lt_or_ge L 2 with hlt | hge
  · -- `1 ≤ L < 2` ⟹ `L = 1`
    obtain rfl : L = 1 := by omega
    exact aoyagi_learning_coefficient_L1 H r B hB hr hpos
  · -- `L ≥ 2`: the direct engine composition — `_gen` fed the engine box-finiteness fit-witness.
    exact aoyagi_learning_coefficient_gen H r B hB hr hL hge hpos
      (Engine.engine_box_threshold_finite (fun s => H s - r) hL
        (fun s => Nat.sub_pos_of_lt (hpos s)))

end DLNFibre.DLN.RLCT
