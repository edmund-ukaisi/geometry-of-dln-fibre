import DLNFibre.Core.Matrix.RankNormalForm

/-!
# `DLNFibre.Core.Matrix.RankNormalFormTriangular` — block-triangular rank normalizers

`rank_normal_form_left_only` (in `RankNormalForm`) carries a rank-`r` matrix with vanishing tail
columns to the block-normal corner `corM` by a single invertible LEFT factor `P` — but `P` is a
generic basis-change unit, with no triangular guarantee. The deepest-point diffeo-bridge needs more:
the endpoint conjugation `U·(prod−B)·V` leaks the joint-Ψ's moved core block into the read blocks
UNLESS the endpoint frames are block-triangular (`endpointP0` block-lower, `endpointQL` block-upper in
the `r ⊕ (·−r)` split). The exact-rational counterexample (`e2-verify/e2_mw2.py`) confirms the leak is
real for non-triangular normalizers.

This module supplies the block-triangular normalizer, under the EXTRA hypothesis that the **leading
`r×r` block is invertible** (the front-pivot condition): then the explicit witness
`P = [[A11⁻¹, 0], [−A21·A11⁻¹, I]]` (block-LOWER) carries `[[A11, 0],[A21, 0]]` to the corner
`[[I,0],[0,0]]`, and its right-only dual (block-UPPER) carries the tail-rows-zero matrix similarly.

CAVEAT (the load-bearing precondition): `[Invertible A11]` is NOT implied by rank-`r` + tail-columns-
zero alone — a rank-`r` corner can carry its rank in the lower rows (e.g. `[[0,0],[1,0]]`, rank 1,
leading block `[0]` singular). The deepest-point boundary corner (`IsDeepLayers`, only tail-columns-
zero, NOT corner-pinned) does not supply it for free; using these for the diffeo bridge needs the
deepest-point construction to pin the boundary corner's leading block invertible (the front-pivot
ripple — see the thread-31 ripple-scope report). Stated here with `A11` invertible explicit, so the
lemma is sound and reusable independent of whether the producer's corner satisfies it.
-/

open Matrix
namespace DLNFibre.Core.Matrix

/-- **Block-LOWER left-normalizer of a front-pivot corner.** For `A = [[A11, 0],[A21, 0]]` (tail
columns zero) with `A11` invertible, the explicit block-lower unit `P = [[⅟A11, 0],[−A21·⅟A11, I]]`
satisfies `P · A = [[I, 0],[0, 0]]` (the block-normal corner), is a unit, and is block-lower
(`toBlocks₁₂ = 0`). The frame the diffeo-bridge's `endpointP0` needs (block-lower kills the conjugation
leak `u12 = 0`). -/
theorem blockLower_left_normalizer {r ar br : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ) (A21 : Matrix (Fin ar) (Fin r) ℝ) [Invertible A11] :
    (Matrix.fromBlocks (⅟A11) 0 (-(A21 * ⅟A11)) (1 : Matrix (Fin ar) (Fin ar) ℝ)).toBlocks₁₂ = 0
    ∧ IsUnit (Matrix.fromBlocks (⅟A11) 0 (-(A21 * ⅟A11)) (1 : Matrix (Fin ar) (Fin ar) ℝ))
    ∧ Matrix.fromBlocks (⅟A11) 0 (-(A21 * ⅟A11)) (1 : Matrix (Fin ar) (Fin ar) ℝ)
        * Matrix.fromBlocks A11 (0 : Matrix (Fin r) (Fin br) ℝ) A21 0
      = Matrix.fromBlocks 1 0 0 0 := by
  letI : Invertible (1 : Matrix (Fin ar) (Fin ar) ℝ) := invertibleOne
  refine ⟨?_, ?_, ?_⟩
  · ext i j; simp [Matrix.toBlocks₁₂, Matrix.fromBlocks]
  · letI : Invertible (Matrix.fromBlocks (⅟A11) 0 (-(A21 * ⅟A11))
        (1 : Matrix (Fin ar) (Fin ar) ℝ)) :=
      Matrix.fromBlocksZero₁₂Invertible (⅟A11) (-(A21 * ⅟A11)) 1
    exact isUnit_of_invertible _
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · rw [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one,
        neg_add_cancel]
    · simp

/-- **Block-UPPER right-normalizer of a tail-rows-zero corner** (the dual). For `A = [[A11, A12],[0, 0]]`
(tail rows zero) with `A11` invertible, the explicit block-upper unit `Q = [[⅟A11, −⅟A11·A12],[0, I]]`
satisfies `A · Q = [[I, 0],[0, 0]]`, is a unit, and is block-upper (`toBlocks₂₁ = 0`). The frame the
diffeo-bridge's `endpointQL` needs (block-upper kills the conjugation leak `v21 = 0`). -/
theorem blockUpper_right_normalizer {r al bl : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ) (A12 : Matrix (Fin r) (Fin bl) ℝ) [Invertible A11] :
    (Matrix.fromBlocks (⅟A11) (-(⅟A11 * A12)) 0 (1 : Matrix (Fin bl) (Fin bl) ℝ)).toBlocks₂₁ = 0
    ∧ IsUnit (Matrix.fromBlocks (⅟A11) (-(⅟A11 * A12)) 0 (1 : Matrix (Fin bl) (Fin bl) ℝ))
    ∧ Matrix.fromBlocks A11 A12 (0 : Matrix (Fin al) (Fin r) ℝ) 0
        * Matrix.fromBlocks (⅟A11) (-(⅟A11 * A12)) 0 (1 : Matrix (Fin bl) (Fin bl) ℝ)
      = Matrix.fromBlocks 1 0 0 0 := by
  letI : Invertible (1 : Matrix (Fin bl) (Fin bl) ℝ) := invertibleOne
  refine ⟨?_, ?_, ?_⟩
  · ext i j; simp [Matrix.toBlocks₂₁, Matrix.fromBlocks]
  · letI : Invertible (Matrix.fromBlocks (⅟A11) (-(⅟A11 * A12)) 0
        (1 : Matrix (Fin bl) (Fin bl) ℝ)) :=
      Matrix.fromBlocksZero₂₁Invertible (⅟A11) (-(⅟A11 * A12)) 1
    exact isUnit_of_invertible _
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul, Matrix.mul_one,
        neg_add_cancel]
    · simp
    · simp

/-! ## Non-vacuity

The lemmas are non-vacuous by exhibition: the explicit witnesses `P = [[⅟A11, 0],[−A21·⅟A11, I]]` and
`Q = [[⅟A11, −⅟A11·A12],[0, I]]` are shown in the statements and proven to satisfy all three properties
(block-triangular, unit, normalizing). The `[Invertible A11]` precondition is inhabited (e.g. `A11 = 1`)
and the normalizer genuinely acts whenever `A21 ≠ 0` (resp. `A12 ≠ 0`): then `P` (resp. `Q`) `≠ 1`
carries the non-normal corner `[[A11,0],[A21,0]]` to `[[I,0],[0,0]]` — not the vacuous already-normal
case. -/

end DLNFibre.Core.Matrix
