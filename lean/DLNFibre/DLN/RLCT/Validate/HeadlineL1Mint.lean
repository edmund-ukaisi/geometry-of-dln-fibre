import DLNFibre.DLN.RLCT.Validate.DeepestBaseL1

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineL1Mint` — the `L = 1` headline endpoint

* **`aoyagi_learning_coefficient_L1`** — the `L = 1` (single-layer) case, UNCONDITIONAL and sorry-free.
  At one layer `prod H A = A 0` (`prod_L1`), so `dlnLoss H B` is the full nondegenerate square-Frobenius
  norm `‖A 0 − B‖²`; the fibre `optimalSet H B = {A | A 0 = B}` is the singleton `{deepestPoint}` (D1 is
  trivial — no other fibre point), and the local RLCT at that point is `H⁰·H¹/2 = aoyagiLambda H r`
  (banked regular-block RLCT `deepest_regular_core_normal_form_L1` + the arithmetic fold
  `reg_shift_add_core_eq_aoyagiLambda`). This is the regular Morse endpoint that the general descent
  (`aoyagi_learning_coefficient_gen`, `hL2 : 2 ≤ L`) cannot reach.

The Engine-based `∀ L ≥ 1` wrapper `aoyagi_learning_coefficient_prestage` was DROPPED with the α-atlas
chart Engine archive (2026-07-20, charter §3): it composed the `L ≥ 2` arm through the retired
`Engine.engine_box_threshold_finite`. The kept `∀ L ≥ 1` conditional headline lives in
`HeadlineConditionalSpine` (route-agnostic `hbox`, no Engine).
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

end DLNFibre.DLN.RLCT
