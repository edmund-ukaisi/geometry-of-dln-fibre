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

/-! ## The boundary forced-decode is a FIXED `ℝ`-linear map of the target

The cert's mechanism crux: with a `q`-INDEPENDENT frame `F`/`Q` (evaluated at wstar), the boundary
decode `D ↦ forcedDecodeLeft F D` / `D ↦ forcedDecodeRight Q D` is `ℝ`-linear in the target `D`
(coefficients `Ring.inverse F₁₁`, `F₂₁`, … are constants), hence a `ContinuousLinearMap`. Applied to
the `O(‖q‖²)` germ `movedC − C`, a fixed CLM contributes no first-order term — which is how
`HasStrictFDerivAt (psiSplitRawGen − id) 0 0` inherits the interior degree-2 vanishing at the boundary. -/

/-- `forcedDecodeLeft F` is `ℝ`-linear in the target `D` (fixed frame `F`). -/
theorem forcedDecodeLeft_isLinear {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (F : Matrix (r ⊕ a) (r ⊕ a) ℝ) :
    IsLinearMap ℝ (fun D : Matrix (r ⊕ a) (r ⊕ b) ℝ => forcedDecodeLeft F D) := by
  refine ⟨fun D D' => ?_, fun c D => ?_⟩
  · show forcedDecodeLeft F (D + D') = forcedDecodeLeft F D + forcedDecodeLeft F D'
    rw [forcedDecodeLeft, forcedDecodeLeft, forcedDecodeLeft, Matrix.fromBlocks_add]
    have e11 : (D + D').toBlocks₁₁ = D.toBlocks₁₁ + D'.toBlocks₁₁ := rfl
    have e12 : (D + D').toBlocks₁₂ = D.toBlocks₁₂ + D'.toBlocks₁₂ := rfl
    have e21 : (D + D').toBlocks₂₁ = D.toBlocks₂₁ + D'.toBlocks₂₁ := rfl
    have e22 : (D + D').toBlocks₂₂ = D.toBlocks₂₂ + D'.toBlocks₂₂ := rfl
    rw [e11, e12, e21, e22]
    congr 1 <;> simp only [Matrix.mul_add] <;> abel
  · show forcedDecodeLeft F (c • D) = c • forcedDecodeLeft F D
    rw [forcedDecodeLeft, forcedDecodeLeft, Matrix.fromBlocks_smul]
    have e11 : (c • D).toBlocks₁₁ = c • D.toBlocks₁₁ := rfl
    have e12 : (c • D).toBlocks₁₂ = c • D.toBlocks₁₂ := rfl
    have e21 : (c • D).toBlocks₂₁ = c • D.toBlocks₂₁ := rfl
    have e22 : (c • D).toBlocks₂₂ = c • D.toBlocks₂₂ := rfl
    rw [e11, e12, e21, e22]
    congr 1 <;> simp only [Matrix.mul_smul, smul_sub]

/-- `forcedDecodeRight Q` is `ℝ`-linear in the target `D` (fixed frame `Q`). -/
theorem forcedDecodeRight_isLinear {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype b] [DecidableEq b]
    (Q : Matrix (r ⊕ b) (r ⊕ b) ℝ) :
    IsLinearMap ℝ (fun D : Matrix (r ⊕ a) (r ⊕ b) ℝ => forcedDecodeRight Q D) := by
  refine ⟨fun D D' => ?_, fun c D => ?_⟩
  · show forcedDecodeRight Q (D + D') = forcedDecodeRight Q D + forcedDecodeRight Q D'
    rw [forcedDecodeRight, forcedDecodeRight, forcedDecodeRight, Matrix.fromBlocks_add]
    have e11 : (D + D').toBlocks₁₁ = D.toBlocks₁₁ + D'.toBlocks₁₁ := rfl
    have e12 : (D + D').toBlocks₁₂ = D.toBlocks₁₂ + D'.toBlocks₁₂ := rfl
    have e21 : (D + D').toBlocks₂₁ = D.toBlocks₂₁ + D'.toBlocks₂₁ := rfl
    have e22 : (D + D').toBlocks₂₂ = D.toBlocks₂₂ + D'.toBlocks₂₂ := rfl
    rw [e11, e12, e21, e22]
    congr 1 <;> simp only [Matrix.add_mul] <;> abel
  · show forcedDecodeRight Q (c • D) = c • forcedDecodeRight Q D
    rw [forcedDecodeRight, forcedDecodeRight, Matrix.fromBlocks_smul]
    have e11 : (c • D).toBlocks₁₁ = c • D.toBlocks₁₁ := rfl
    have e12 : (c • D).toBlocks₁₂ = c • D.toBlocks₁₂ := rfl
    have e21 : (c • D).toBlocks₂₁ = c • D.toBlocks₂₁ := rfl
    have e22 : (c • D).toBlocks₂₂ = c • D.toBlocks₂₂ := rfl
    rw [e11, e12, e21, e22]
    congr 1 <;> simp only [Matrix.smul_mul, smul_sub]

/-- The layer-0 forced-decode as a `ContinuousLinearMap` (fixed frame `F`). -/
noncomputable def forcedDecodeLeftCLM {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] [Fintype b]
    (F : Matrix (r ⊕ a) (r ⊕ a) ℝ) :
    Matrix (r ⊕ a) (r ⊕ b) ℝ →L[ℝ] Matrix (r ⊕ a) (r ⊕ b) ℝ :=
  LinearMap.toContinuousLinearMap ((forcedDecodeLeft_isLinear F).mk' _)

/-- The last-layer forced-decode as a `ContinuousLinearMap` (fixed frame `Q`). -/
noncomputable def forcedDecodeRightCLM {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [Fintype b] [DecidableEq b]
    (Q : Matrix (r ⊕ b) (r ⊕ b) ℝ) :
    Matrix (r ⊕ a) (r ⊕ b) ℝ →L[ℝ] Matrix (r ⊕ a) (r ⊕ b) ℝ :=
  LinearMap.toContinuousLinearMap ((forcedDecodeRight_isLinear Q).mk' _)

@[simp] theorem coe_forcedDecodeLeftCLM {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] [Fintype b]
    (F : Matrix (r ⊕ a) (r ⊕ a) ℝ) :
    ⇑(forcedDecodeLeftCLM (b := b) F) = fun D => forcedDecodeLeft F D :=
  rfl

@[simp] theorem coe_forcedDecodeRightCLM {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [Fintype b] [DecidableEq b]
    (Q : Matrix (r ⊕ b) (r ⊕ b) ℝ) :
    ⇑(forcedDecodeRightCLM (a := a) Q) = fun D => forcedDecodeRight Q D :=
  rfl

/-! ## The moved chain is fixed where the down-blocks vanish (`hraw0` core / the germ value at `0`)

At the deepest point every chain layer has `toBlocks₂₁ = 0` (banked
`deepestChain_wstar_toBlocks₂₁_eq_zero`). Then the whole edit collapses: `vDown = 0` ⟹ `nMix = 1`,
`Kcoup = 0` ⟹ `schurTilde = blockSchur = toBlocks₂₂`, `upEdit = 0`, `hTermLC = 0` ⟹ `deltaV0 = 0` ⟹
`Z0edit0 = 0`, so `movedC C (Z0edit0 C L) = C`. This is the VALUE of the `movedC − C` germ at `0`
(vanishing to order ≥ 3 there per the de-risk cert) and the algebraic core of `psiSplitRawGen 0 = 0`. -/

section MovedFixed
variable {r : Type*} [Fintype r] [DecidableEq r] {α : Type*} [CommRing α]
  {m : ℕ → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- **The moved chain is fixed on a `toBlocks₂₁ = 0` chain.** If every layer of `C` has zero
down-block (`(C k).toBlocks₂₁ = 0`), the whole moved-chain edit is trivial: `movedC C (Z0edit0 C L) s
= C s` for every `s`. -/
theorem movedC_eq_self_of_toBlocks₂₁_zero
    (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ)
    (hZ : ∀ k, (C k).toBlocks₂₁ = 0) (s : ℕ) :
    movedC C (Z0edit0 C L) s = C s := by
  have hvDown : ∀ k, vDown C k = 0 := fun k => by
    simp only [vDown, hZ k, Matrix.zero_mul]
  have hKcoup : ∀ k, Kcoup C k = 0 := fun k => by
    simp only [Kcoup, hZ k, Matrix.zero_mul]
  have hblockSchur : ∀ k, blockSchur (C k) = (C k).toBlocks₂₂ := fun k => by
    simp only [blockSchur, hZ k, Matrix.zero_mul, sub_zero]
  have hschurTilde : ∀ k, schurTilde C k = blockSchur (C k) := fun k => by
    simp only [schurTilde, hKcoup k, sub_zero, Matrix.one_mul]
  have hupEdit : ∀ k, upEdit C k = 0 := fun k => by
    simp only [upEdit, hschurTilde k, sub_self, Matrix.mul_zero]
  have hmovedY : ∀ k, movedY C k = (C k).toBlocks₁₂ := fun k => by
    simp only [movedY, hupEdit k, add_zero]
  have hTermLC0 : ∀ j, hTermLC C j = 0 := fun j => by
    simp only [hTermLC, hvDown j, Matrix.mul_zero, Matrix.zero_mul]
  have hdeltaV0 : deltaV0 C L = 0 := by
    simp only [deltaV0]; exact Finset.sum_eq_zero (fun j _ => hTermLC0 j)
  have hZ0edit0 : Z0edit0 C L = 0 := by
    simp only [Z0edit0, hZ 0, hdeltaV0, Matrix.zero_mul, add_zero]
  have hmovedZ : ∀ k, movedZ C (Z0edit0 C L) k = (C k).toBlocks₂₁ := fun k => by
    cases k with
    | zero => rw [hZ 0]; exact hZ0edit0
    | succ n => rfl
  have hmovedT : ∀ k, movedT C (Z0edit0 C L) k = (C k).toBlocks₂₂ := fun k => by
    simp only [movedT, hmovedZ k, hZ k, Matrix.zero_mul, add_zero, hschurTilde k, hblockSchur k]
  rw [movedC, hmovedY s, hmovedZ s, hmovedT s, Matrix.fromBlocks_toBlocks]

end MovedFixed

end DLNFibre.DLN.RLCT
