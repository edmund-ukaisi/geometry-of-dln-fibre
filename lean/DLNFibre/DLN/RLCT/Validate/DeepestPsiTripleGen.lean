import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGen

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiTripleGen` — Producer 1 building blocks (#120 `hstep2`)

Building blocks for the general-`L` diffeo triple of `psiSplitRawGen` (`DeepestPsiSplitRawGen`).
The first block is the **two-sided-unit identity-read recovery `(★)`** the de-risk cert
(`genm-hstep2triderisk/cert.md`) flags as the one spot where the direction of the frame-corner
inverse matters: the boundary `forcedDecode` genuinely inverts the boundary framing.

* `forcedDecodeLeft_lowerFrame_mul` — `forcedDecodeLeft (fromBlocks F11 0 F21 1) ((fromBlocks F11 0 F21 1) * R) = R`
  for a UNIT corner `F11` (`(★)` left mirror; uses the LEFT inverse `Ring.inverse F11 * F11 = 1`).
* `forcedDecodeRight_upperFrame_mul` — `forcedDecodeRight (fromBlocks Q11 Q12 0 1) (R * (fromBlocks Q11 Q12 0 1)) = R`
  for a UNIT corner `Q11` (`(★)` right mirror; uses the RIGHT inverse `Q11 * Ring.inverse Q11 = 1`).

NOTE (de-risk): the banked `fromBlocks_lowerFrame_mul_forcedDecode` / `_rightUpper_`
(`DeepestFramedBoundaryMove`) are stated with the OPPOSITE one-sided inverse (`frame · decode = target`);
`(★)` is the OTHER composition (`decode (frame · R) = R`), needing the two-sidedness of the unit
(`deepBlkA_isUnit_gen` etc. downstream). Pure `fromBlocks` block algebra over `ℝ`.
-/

open Matrix

namespace DLNFibre.DLN.RLCT

/-- **`(★)` left mirror — identity-read recovery for the layer-0 block-LOWER frame.** With a unit corner
`F11`, the forced left-decode inverts the frame: `forcedDecodeLeft (fromBlocks F11 0 F21 1) ((fromBlocks
F11 0 F21 1) * R) = R`. Uses `Ring.inverse F11 * F11 = 1` (LEFT inverse — the direction the banked
`fromBlocks_lowerFrame_mul_forcedDecode` does NOT use). -/
theorem forcedDecodeLeft_lowerFrame_mul {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (F11 : Matrix r r ℝ) (F21 : Matrix a r ℝ) (R : Matrix (r ⊕ a) (r ⊕ b) ℝ)
    (hF11 : IsUnit F11) :
    forcedDecodeLeft (Matrix.fromBlocks F11 0 F21 1) (Matrix.fromBlocks F11 0 F21 1 * R) = R := by
  set Pinv := Ring.inverse F11 with hPinv
  have hinv : Pinv * F11 = 1 := Ring.inverse_mul_cancel F11 hF11
  -- Expand `R` and `F * R` into block form.
  have hR : R = Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂ R.toBlocks₂₁ R.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks R).symm
  have hmul : Matrix.fromBlocks F11 (0 : Matrix r a ℝ) F21 (1 : Matrix a a ℝ) * R
      = Matrix.fromBlocks (F11 * R.toBlocks₁₁) (F11 * R.toBlocks₁₂)
          (F21 * R.toBlocks₁₁ + R.toBlocks₂₁) (F21 * R.toBlocks₁₂ + R.toBlocks₂₂) := by
    conv_lhs => rw [hR]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, add_zero, Matrix.one_mul]
  -- Compute the four decoded blocks.
  rw [forcedDecodeLeft, hmul]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  have h11 : Pinv * (F11 * R.toBlocks₁₁) = R.toBlocks₁₁ := by
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have h12 : Pinv * (F11 * R.toBlocks₁₂) = R.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [h11, h12]
  conv_rhs => rw [hR]
  congr 1 <;> abel

/-- **`(★)` right mirror — identity-read recovery for the last-layer block-UPPER frame.** With a unit
corner `Q11`, the forced right-decode inverts the frame: `forcedDecodeRight (fromBlocks Q11 Q12 0 1) (R *
(fromBlocks Q11 Q12 0 1)) = R`. Uses `Q11 * Ring.inverse Q11 = 1` (RIGHT inverse — the direction the
banked `fromBlocks_rightUpper_mul_forcedDecode` does NOT use). -/
theorem forcedDecodeRight_upperFrame_mul {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype b] [DecidableEq b]
    (Q11 : Matrix r r ℝ) (Q12 : Matrix r b ℝ) (R : Matrix (r ⊕ a) (r ⊕ b) ℝ)
    (hQ11 : IsUnit Q11) :
    forcedDecodeRight (Matrix.fromBlocks Q11 Q12 0 1) (R * Matrix.fromBlocks Q11 Q12 0 1) = R := by
  set Qinv := Ring.inverse Q11 with hQinv
  have hinv : Q11 * Qinv = 1 := Ring.mul_inverse_cancel Q11 hQ11
  have hR : R = Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂ R.toBlocks₂₁ R.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks R).symm
  have hmul : R * Matrix.fromBlocks Q11 Q12 (0 : Matrix b r ℝ) (1 : Matrix b b ℝ)
      = Matrix.fromBlocks (R.toBlocks₁₁ * Q11) (R.toBlocks₁₁ * Q12 + R.toBlocks₁₂)
          (R.toBlocks₂₁ * Q11) (R.toBlocks₂₁ * Q12 + R.toBlocks₂₂) := by
    conv_lhs => rw [hR]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.mul_one]
  rw [forcedDecodeRight, hmul]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  have h11 : R.toBlocks₁₁ * Q11 * Qinv = R.toBlocks₁₁ := by
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  have h21 : R.toBlocks₂₁ * Q11 * Qinv = R.toBlocks₂₁ := by
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [h11, h21]
  conv_rhs => rw [hR]
  congr 1 <;> abel

end DLNFibre.DLN.RLCT
