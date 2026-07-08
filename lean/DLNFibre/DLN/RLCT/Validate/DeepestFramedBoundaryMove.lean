import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitGenMoved
import DLNFibre.DLN.RLCT.Validate.DeepestBlockDecomp

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedBoundaryMove` — the boundary-frame move identity

Item-2 core of #120 `hstep2`. The **verified abstract core of the `genm-hstep2germs6` design
CORRECTION**. The prior tide found that the frame-BLIND `psiSplitRawGen` reads (`Y'_s := movedY (Cq_s)`,
etc.) fail the framed-chain move identity at the two BOUNDARY layers, because `framedParamsPivot`
conjugates each layer by the endpoint gauge frames `Pf_s · (·) · Qf_s`. The interior frames are the
identity (guaranteed by the triangular bundle, `DeepestPivotFrameTriangular`), so interior layers stay
frame-blind; the two boundary layers need FRAME-DEPENDENT reads. This module discharges, at the
network-free `Type` level, the two facts the correction rests on:

* **The boundary move identity** (`fromBlocks_lowerFrame_mul_forcedDecode` / `_rightUpper_`): with a
  block-LOWER left frame `fromBlocks P11 0 P21 1` (identity `₂₂`-block) and the FORCED frame-dependent
  reads `decode = fromBlocks (Pinv·A) (Pinv·Y) (Z − P21·Pinv·A) (T − P21·Pinv·Y)`, the framed layer
  `frame · decode` reconstructs the LITERAL target `fromBlocks A Y Z T`. Symmetric for a block-UPPER
  right frame. Instantiated at `A = (C s)₁₁`, `Y = movedY C s`, `Z = movedZ`, `T = movedT`, these are
  exactly the corrected layer-0 / last-layer reads (`Y'_0 = P11⁻¹·movedY`, `Z'_0 = Z0edit − P21·X`,
  `T'_0 = movedT − P21·P11⁻¹·movedY`), producing `movedC` blockwise.

* **Schur-invisibility of the one-sided ₂₂=1 frame** (`blockSchur_lowerFrame_left` /
  `blockSchur_rightUpper_right`): `blockSchur (fromBlocks P11 0 P21 1 · M) = blockSchur M` (and the
  mirror for a right block-upper frame). This is the specialization of the banked two-sided
  `schur_frame_transform` (`DeepestBlockDecomp`) to `DP = DQ = 1`, bridged from its `(·)⁻¹` spelling to
  `blockSchur`'s `Ring.inverse` spelling. It keeps `hsub4core` consistent: the frame-free decode Schur
  core at each boundary layer equals `blockSchur (movedC C_s)`, so the boundary frames do not leak into
  the `Score` product (Codex-computed, `codex/move-identity-frame2-answer.md` Q1).

## Status
Pure `Matrix`/`Ring` algebra over a general `CommRing` (the block move identities) resp. over `ℝ` (the
Schur-invisibility, inherited from `schur_frame_transform`'s `ℝ` statement). No `deepestSplit`, no
`Params`, no `Fin`-width casts. The invertibility of the frame corner `P11` / `Q11` enters as an
explicit two-sided inverse hypothesis (`P11 · Pinv = 1`); at the deepest point these hold (the frame
corners are units).
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## The boundary block move identity (pure `CommRing` block algebra) -/

section BlockMove
variable {r a b : Type*} [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] {α : Type*} [CommRing α]

/-- **Layer-0 boundary move identity (block-lower left frame, `₂₂ = 1`).** With a block-lower frame
`fromBlocks P11 0 P21 1` and a right inverse `Pinv` of `P11` (`P11 · Pinv = 1`), the FORCED reads
`fromBlocks (Pinv·A) (Pinv·Y) (Z − P21·(Pinv·A)) (T − P21·(Pinv·Y))` reconstruct the LITERAL target
`fromBlocks A Y Z T` under the frame. This is the layer-0 half of the `germs6` correction: at
`A = (C 0)₁₁`, `Y = movedY C 0`, `Z = movedZ C Z0edit 0`, `T = movedT C Z0edit 0`, the framed decode
equals `movedC C Z0edit 0` blockwise. Pure `fromBlocks_multiply` + the `P11·Pinv = 1` cancel. -/
theorem fromBlocks_lowerFrame_mul_forcedDecode
    (P11 Pinv : Matrix r r α) (P21 : Matrix a r α)
    (A : Matrix r r α) (Y : Matrix r b α) (Z : Matrix a r α) (T : Matrix a b α)
    (hP : P11 * Pinv = 1) :
    Matrix.fromBlocks P11 (0 : Matrix r a α) P21 (1 : Matrix a a α)
        * Matrix.fromBlocks (Pinv * A) (Pinv * Y) (Z - P21 * (Pinv * A)) (T - P21 * (Pinv * Y))
      = Matrix.fromBlocks A Y Z T := by
  rw [Matrix.fromBlocks_multiply]
  have h11 : P11 * (Pinv * A) + (0 : Matrix r a α) * (Z - P21 * (Pinv * A)) = A := by
    rw [Matrix.zero_mul, add_zero, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  have h12 : P11 * (Pinv * Y) + (0 : Matrix r a α) * (T - P21 * (Pinv * Y)) = Y := by
    rw [Matrix.zero_mul, add_zero, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  have h21 : P21 * (Pinv * A) + (1 : Matrix a a α) * (Z - P21 * (Pinv * A)) = Z := by
    rw [Matrix.one_mul]; abel
  have h22 : P21 * (Pinv * Y) + (1 : Matrix a a α) * (T - P21 * (Pinv * Y)) = T := by
    rw [Matrix.one_mul]; abel
  rw [h11, h12, h21, h22]

/-- **Last-layer boundary move identity (block-upper right frame, `₂₂ = 1`).** With a block-upper
frame `fromBlocks Q11 Q12 0 1` (the invertible `r×r` corner is `Q11`; the identity `₂₂`-block is on the
core width `b`) and a left inverse `Qinv` of `Q11` (`Qinv · Q11 = 1`), the FORCED reads
`fromBlocks (A·Qinv) (Y − (A·Qinv)·Q12) (Z·Qinv) (T − (Z·Qinv)·Q12)` reconstruct the LITERAL target
`fromBlocks A Y Z T` under the frame. This is the symmetric last-layer half of the `germs6`
correction (the mirror of the layer-0 read via `deepBlkZ_last`). Pure `fromBlocks_multiply` + the
`Qinv·Q11 = 1` cancel. -/
theorem fromBlocks_rightUpper_mul_forcedDecode
    (Q11 Qinv : Matrix r r α) (Q12 : Matrix r b α)
    (A : Matrix r r α) (Y : Matrix r b α) (Z : Matrix a r α) (T : Matrix a b α)
    (hQ : Qinv * Q11 = 1) :
    Matrix.fromBlocks (A * Qinv) (Y - A * Qinv * Q12) (Z * Qinv) (T - Z * Qinv * Q12)
        * Matrix.fromBlocks Q11 Q12 (0 : Matrix b r α) (1 : Matrix b b α)
      = Matrix.fromBlocks A Y Z T := by
  rw [Matrix.fromBlocks_multiply]
  have h11 : A * Qinv * Q11 + (Y - A * Qinv * Q12) * (0 : Matrix b r α) = A := by
    rw [Matrix.mul_zero, add_zero, Matrix.mul_assoc, hQ, Matrix.mul_one]
  have h12 : A * Qinv * Q12 + (Y - A * Qinv * Q12) * (1 : Matrix b b α) = Y := by
    rw [Matrix.mul_one]; abel
  have h21 : Z * Qinv * Q11 + (T - Z * Qinv * Q12) * (0 : Matrix b r α) = Z := by
    rw [Matrix.mul_zero, add_zero, Matrix.mul_assoc, hQ, Matrix.mul_one]
  have h22 : Z * Qinv * Q12 + (T - Z * Qinv * Q12) * (1 : Matrix b b α) = T := by
    rw [Matrix.mul_one]; abel
  rw [h11, h12, h21, h22]

end BlockMove

/-! ## Schur-invisibility of the one-sided `₂₂ = 1` boundary frame (over `ℝ`) -/

section SchurFrame
variable {r s t : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
  [Fintype t] [DecidableEq t]

/-- Bridge: for an invertible `X`, `blockSchur`'s `Ring.inverse X` pivot equals the `X⁻¹`
`schur_frame_transform` produces. -/
private theorem ringInverse_eq_nonsing {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) [Invertible X] : Ring.inverse X = X⁻¹ := by
  rw [Ring.inverse_invertible, invOf_eq_nonsing_inv]

/-- **Schur-invisibility of a block-LOWER left frame with identity `₂₂`-block.** For a middle
`M = fromBlocks A B C D` with `A` and the framed `(1,1)` corner invertible,
`blockSchur (fromBlocks P11 0 P21 1 · M) = blockSchur M`. The specialization of the banked two-sided
`schur_frame_transform` to a trivial right frame (`Q = 1`) and identity bottom-right frame block
(`DP = 1`): the lower frame's `P11, P21` fully cancel through the pivot inverse. Consumed by
`hsub4core` to show the layer-0 boundary frame does not leak into the `Score` Schur product. -/
theorem blockSchur_lowerFrame_left
    (P11 : Matrix r r ℝ) (P21 : Matrix s r ℝ)
    (A : Matrix r r ℝ) (B : Matrix r t ℝ) (C : Matrix s r ℝ) (D : Matrix s t ℝ)
    [Invertible P11] [Invertible A]
    [Invertible (Matrix.fromBlocks P11 (0 : Matrix r s ℝ) P21 (1 : Matrix s s ℝ)
        * Matrix.fromBlocks A B C D).toBlocks₁₁] :
    blockSchur (Matrix.fromBlocks P11 (0 : Matrix r s ℝ) P21 (1 : Matrix s s ℝ)
          * Matrix.fromBlocks A B C D)
      = blockSchur (Matrix.fromBlocks A B C D) := by
  set N := Matrix.fromBlocks P11 (0 : Matrix r s ℝ) P21 (1 : Matrix s s ℝ)
    * Matrix.fromBlocks A B C D with hN
  -- `blockSchur N` in the `(·)⁻¹` spelling (its `(1,1)` corner is invertible by hypothesis).
  have hbs : blockSchur N = N.toBlocks₂₂ - N.toBlocks₂₁ * (N.toBlocks₁₁)⁻¹ * N.toBlocks₁₂ := by
    rw [blockSchur, ringInverse_eq_nonsing]
  rw [hbs, hN]
  -- Insert the trivial right frame, apply `schur_frame_transform` (DP = DQ = 1), collapse.
  haveI : Invertible (1 : Matrix r r ℝ) := invertibleOne
  have hkey := schur_frame_transform P11 P21 (1 : Matrix s s ℝ) A B C D
      (1 : Matrix r r ℝ) (0 : Matrix r t ℝ) (1 : Matrix t t ℝ)
  rw [Matrix.fromBlocks_one, Matrix.mul_one] at hkey
  rw [hkey, Matrix.one_mul, Matrix.mul_one, blockSchur,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂, ringInverse_eq_nonsing A]

/-- **Schur-invisibility of a block-UPPER right frame with identity `₂₂`-block.** For a middle
`M = fromBlocks A B C D` with `A` and the framed `(1,1)` corner invertible, and a block-upper right
frame `fromBlocks Q11 Q12 0 1` (invertible `r×r` corner `Q11`, identity `₂₂`-block on width `t`),
`blockSchur (M · fromBlocks Q11 Q12 0 1) = blockSchur M`. The mirror of `blockSchur_lowerFrame_left`
(trivial LEFT frame `P = 1`, `DP = 1`); the upper frame's `Q11, Q12` cancel. Consumed by `hsub4core`
for the last-layer boundary frame. -/
theorem blockSchur_rightUpper_right
    (Q11 : Matrix r r ℝ) (Q12 : Matrix r t ℝ)
    (A : Matrix r r ℝ) (B : Matrix r t ℝ) (C : Matrix s r ℝ) (D : Matrix s t ℝ)
    [Invertible Q11] [Invertible A]
    [Invertible (Matrix.fromBlocks A B C D
        * Matrix.fromBlocks Q11 Q12 (0 : Matrix t r ℝ) (1 : Matrix t t ℝ)).toBlocks₁₁] :
    blockSchur (Matrix.fromBlocks A B C D
          * Matrix.fromBlocks Q11 Q12 (0 : Matrix t r ℝ) (1 : Matrix t t ℝ))
      = blockSchur (Matrix.fromBlocks A B C D) := by
  set N := Matrix.fromBlocks A B C D
    * Matrix.fromBlocks Q11 Q12 (0 : Matrix t r ℝ) (1 : Matrix t t ℝ) with hN
  have hbs : blockSchur N = N.toBlocks₂₂ - N.toBlocks₂₁ * (N.toBlocks₁₁)⁻¹ * N.toBlocks₁₂ := by
    rw [blockSchur, ringInverse_eq_nonsing]
  rw [hbs, hN]
  -- Insert the trivial left frame `P = 1 = fromBlocks 1 0 0 1`, apply `schur_frame_transform`.
  haveI : Invertible (1 : Matrix r r ℝ) := invertibleOne
  have hkey := schur_frame_transform (1 : Matrix r r ℝ) (0 : Matrix s r ℝ) (1 : Matrix s s ℝ)
      A B C D Q11 Q12 (1 : Matrix t t ℝ)
  rw [Matrix.fromBlocks_one, Matrix.one_mul] at hkey
  rw [hkey, Matrix.one_mul, Matrix.mul_one, blockSchur,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂, ringInverse_eq_nonsing A]

end SchurFrame

end DLNFibre.DLN.RLCT
