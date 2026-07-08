import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGenMove
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback
import DLNFibre.DLN.RLCT.Validate.DeepestHmoveGen
import DLNFibre.DLN.RLCT.Validate.DeepestDeepBlkBoundaryGen
import DLNFibre.DLN.RLCT.Validate.DeepestFramedBoundaryMove
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction
import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitGenLeftCol

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestHsub4coreHCGen` — the general-`L` `hC` core-side move readback
(#120 `hstep2`, item 3, Piece 1)

The `hC` hypothesis the general-`L` keystone in `DeepestHsub4coreGen` consumes: at the chart point
`q = split x`, the conjugated absorbed core of the moved point `psiSplitRawGen … q`, reindexed,
equals the moved Schur core of the **decode** chain of `x`.

## Building blocks (bottom-up)

* `absorbedCoreConj_eq_blockSchur_synthetic` — the GENERIC algebraic reduction: the conjugated
  absorbed core `coreRead + schurCorrectionConj` is the `(1,1)`-Schur complement of the synthetic
  layer `fromBlocks (deepBlkA+X) (deepBlkY+Y) (deepBlkZ+Z) coreRead`. Pure `Matrix`/`Ring` algebra
  (`nonsing_inv_eq_ringInverse` bridges the `⁻¹` to `blockSchur`'s `Ring.inverse`).
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## The generic conjugated-absorbed-core = synthetic-layer Schur complement -/

/-- **The conjugated absorbed core is a `(1,1)`-Schur complement.** For any core slot `pc`, gauge
slot `pg`, `coreRead pc s + schurCorrectionConj pg s` equals `blockSchur` of the synthetic layer
with blocks the deepest constants plus the gauge/core reads (`(1,1)=deepBlkA+gaugeReadX`,
`(1,2)=deepBlkY+gaugeReadY`, `(2,1)=deepBlkZ+gaugeReadZ`, `(2,2)=coreRead`). Pure algebra
(`blockSchur (fromBlocks A' Y' Z' T') = T'−Z'·(A')⁻¹·Y'`, via `nonsing_inv_eq_ringInverse`). -/
theorem absorbedCoreConj_eq_blockSchur_synthetic (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (pc : Fin (flatDim (deepestM H r)) → ℝ)
    (pg : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) (s : Fin L) :
    (paramsEquivFlat (deepestM H r)).symm pc s + schurCorrectionConj H r B hB hr hL pg s
      = blockSchur (Matrix.fromBlocks
          (deepBlkA H r B hB hr hL s + gaugeReadX H r hr hL pg s)
          (deepBlkY H r B hB hr hL s + gaugeReadY H r hr hL pg s)
          (deepBlkZ H r B hB hr hL s + gaugeReadZ H r hr hL pg s)
          ((paramsEquivFlat (deepestM H r)).symm pc s)) := by
  rw [blockSchur, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, schurCorrectionConj,
    ← Matrix.nonsing_inv_eq_ringInverse]
  rw [Matrix.neg_mul, Matrix.neg_mul, ← sub_eq_add_neg]

/-! ## The `toBlocks₁₂/₂₁/₂₂` decode-chain layer bridges (`k < L`)

The `₁₂/₂₁/₂₂` analogues of the banked `deepestChain_toBlocks₁₁_eq_layer`: the off-diagonal / core
blocks of the decode-chain layer are the `rThresholdSplit`-layer blocks of `A ⟨k, hk⟩`, up to the
reduced-width `finCongr` relabel — matching the reindex convention of the framed-chain block lemma
`deepestChain_framedParamsPivot_blocks_of_frame_one`. -/

/-- Decode-chain layer `(1,2)` block. -/
theorem deepestChain_toBlocks₁₂_eq_layer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L) :
    (deepestChain H r hr A k).toBlocks₁₂
      = Matrix.reindex (Equiv.refl (Fin r)) (finCongr (chainWidth_succ_sub H r ⟨k, hk⟩))
          (Matrix.reindex (rThresholdSplit r (H (⟨k, hk⟩ : Fin L).castSucc) (hr _))
            (rThresholdSplit r (H (⟨k, hk⟩ : Fin L).succ) (hr _)) (A ⟨k, hk⟩)).toBlocks₁₂ := by
  funext i j
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, deepestChain, deepestChainLayer, dif_pos hk,
    deepestChainSplit, rThresholdSplit_symm_inl, rThresholdSplit_symm_inr, finCongr_symm,
    finCongr_apply]
  congr 1

/-- Decode-chain layer `(2,1)` block. -/
theorem deepestChain_toBlocks₂₁_eq_layer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L) :
    (deepestChain H r hr A k).toBlocks₂₁
      = Matrix.reindex (finCongr (chainWidth_castSucc_sub H r ⟨k, hk⟩)) (Equiv.refl (Fin r))
          (Matrix.reindex (rThresholdSplit r (H (⟨k, hk⟩ : Fin L).castSucc) (hr _))
            (rThresholdSplit r (H (⟨k, hk⟩ : Fin L).succ) (hr _)) (A ⟨k, hk⟩)).toBlocks₂₁ := by
  funext i j
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, deepestChain, deepestChainLayer, dif_pos hk,
    deepestChainSplit, rThresholdSplit_symm_inl, rThresholdSplit_symm_inr, finCongr_symm,
    finCongr_apply]
  congr 1

/-- Decode-chain layer `(2,2)` block. -/
theorem deepestChain_toBlocks₂₂_eq_layer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L) :
    (deepestChain H r hr A k).toBlocks₂₂
      = Matrix.reindex (finCongr (chainWidth_castSucc_sub H r ⟨k, hk⟩))
          (finCongr (chainWidth_succ_sub H r ⟨k, hk⟩))
          (Matrix.reindex (rThresholdSplit r (H (⟨k, hk⟩ : Fin L).castSucc) (hr _))
            (rThresholdSplit r (H (⟨k, hk⟩ : Fin L).succ) (hr _)) (A ⟨k, hk⟩)).toBlocks₂₂ := by
  funext i j
  simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    deepestChain, deepestChainLayer, dif_pos hk, deepestChainSplit,
    rThresholdSplit_symm_inr, finCongr_symm, finCongr_apply]
  congr 1

/-! ## Interior-vanishing of the deepest `(2,1)` and `(2,2)` blocks (lemma 2)

The `deepBlkZ` / `deepBlkT` analogues of the banked `deepBlkY_interior_zero`: at a strict-interior layer
the deepest point is the corner `diag(I_r, 0)` (`deepestPoint_interior_eq_corM`), whose rows `≥ r` all
vanish; `toBlocks₂₁` reads rows `≥ r`, cols `< r` and `toBlocks₂₂` reads rows `≥ r`, cols `≥ r`. -/

/-- **`deepBlkZ_s = 0` at interior layers** (`0 < s`, `s+1 < L`): `toBlocks₂₁` reads rows `≥ r`, which
the corner `diag(I_r, 0)` kills (the `(i = j ∧ i < r)` guard fails since `i ≥ r`). -/
theorem deepBlkZ_interior_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L) :
    deepBlkZ H r B hB hr hL s = 0 := by
  funext i j
  change (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inl j)) = 0
  rw [deepestPoint_interior_eq_corM H r B hB hr hL s hpos hlt,
    rThresholdSplit_symm_inr, rThresholdSplit_symm_inl]
  simp only [Matrix.of_apply]
  rw [if_neg]
  rintro ⟨_, hlt'⟩
  omega

/-- **`deepBlkT_s = 0` at interior layers** (`0 < s`, `s+1 < L`): the deepest `(2,2)` block reads rows
`≥ r`, killed by the corner exactly as `deepBlkZ`. -/
theorem deepBlkT_interior_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L) :
    (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0 := by
  funext i j
  show (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr j)) = 0
  rw [deepestPoint_interior_eq_corM H r B hB hr hL s hpos hlt,
    rThresholdSplit_symm_inr, rThresholdSplit_symm_inr]
  simp only [Matrix.of_apply]
  rw [if_neg]
  rintro ⟨_, hlt'⟩
  omega

/-! ## Abstract: endpoint frames preserve `Kcoup` and per-layer `blockSchur`

The core-side counterpart of the reg-side `regBlocks_movedC`. Working over the same abstract `r ⊕ ·`
chain as `DeepestPsiSplitGenMoved`: a block-**lower** frame `PL` at layer `0` (identity `₂₂`-block, unit
`₁₁`-corner) and a block-**upper** frame `QU` at the last layer `M` leave every off-pivot coupling `Kcoup`
and every per-layer `blockSchur` unchanged. The `P11`/`Q11` factors cancel through `Kcoup`'s inverse
(`conj_ringInverse_cancel`); `blockSchur` is frame-invisible by direct block algebra. -/

section AbstractFrame

variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
  {m : ℕ → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- Left-frame `Ring.inverse` cancel: `Ring.inverse (P * B) * P = Ring.inverse B` (`P`, `B` units). -/
theorem leftFrame_ringInverse_cancel {n : Type*} [Fintype n] [DecidableEq n]
    (P B : Matrix n n ℝ) (hP : IsUnit P) (hB : IsUnit B) :
    Ring.inverse (P * B) * P = Ring.inverse B := by
  letI iP := hP.invertible
  letI iB := hB.invertible
  letI : Invertible (P * B) := iP.mul iB
  rw [Ring.inverse_invertible, Ring.inverse_invertible, invOf_mul P B, Matrix.mul_assoc,
    invOf_mul_self, Matrix.mul_one]

/-- Right-frame `Ring.inverse` cancel: `Q * Ring.inverse (B * Q) = Ring.inverse B` (`Q`, `B` units). -/
theorem rightFrame_ringInverse_cancel {n : Type*} [Fintype n] [DecidableEq n]
    (Q B : Matrix n n ℝ) (hQ : IsUnit Q) (hB : IsUnit B) :
    Q * Ring.inverse (B * Q) = Ring.inverse B := by
  letI iQ := hQ.invertible
  letI iB := hB.invertible
  letI : Invertible (B * Q) := iB.mul iQ
  rw [Ring.inverse_invertible, Ring.inverse_invertible, invOf_mul B Q, mul_invOf_cancel_left]

/-- Conjugating-frame `Ring.inverse` cancel: `Q * Ring.inverse (P * B * Q) * P = Ring.inverse B`. -/
theorem conj_ringInverse_cancel {n : Type*} [Fintype n] [DecidableEq n]
    (P B Q : Matrix n n ℝ) (hP : IsUnit P) (hB : IsUnit B) (hQ : IsUnit Q) :
    Q * Ring.inverse (P * B * Q) * P = Ring.inverse B := by
  letI iP := hP.invertible
  letI iB := hB.invertible
  letI iQ := hQ.invertible
  letI iPB : Invertible (P * B) := iP.mul iB
  letI : Invertible (P * B * Q) := iPB.mul iQ
  rw [Ring.inverse_invertible, Ring.inverse_invertible, invOf_mul (P * B) Q, invOf_mul P B,
    mul_invOf_cancel_left, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]

/-- **A block-lower left frame is `blockSchur`-invisible.** With `PL.toBlocks₁₂ = 0`, `PL.toBlocks₂₂ = 1`
and units on `PL.toBlocks₁₁`, `M.toBlocks₁₁`, `blockSchur (PL * M) = blockSchur M`. Direct block algebra
(no appeal to `blockSchur_lowerFrame_left`; the `P11` cancels through the pivot inverse). -/
theorem blockSchur_lowerFrame_of_blocks {σ τ : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ]
    (PL : Matrix (ρ ⊕ σ) (ρ ⊕ σ) ℝ) (Mm : Matrix (ρ ⊕ σ) (ρ ⊕ τ) ℝ)
    (hPl12 : PL.toBlocks₁₂ = 0) (hPl22 : PL.toBlocks₂₂ = 1)
    (hPl11 : IsUnit PL.toBlocks₁₁) (hM11 : IsUnit Mm.toBlocks₁₁) :
    blockSchur (PL * Mm) = blockSchur Mm := by
  have hPM : PL * Mm = Matrix.fromBlocks (PL.toBlocks₁₁ * Mm.toBlocks₁₁) (PL.toBlocks₁₁ * Mm.toBlocks₁₂)
      (PL.toBlocks₂₁ * Mm.toBlocks₁₁ + Mm.toBlocks₂₁) (PL.toBlocks₂₁ * Mm.toBlocks₁₂ + Mm.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks PL, ← Matrix.fromBlocks_toBlocks Mm]
    rw [Matrix.fromBlocks_multiply, hPl12, hPl22]
    simp only [Matrix.zero_mul, add_zero, Matrix.one_mul]
  have hMcancel : Mm.toBlocks₁₁ * (Ring.inverse Mm.toBlocks₁₁ * Mm.toBlocks₁₂) = Mm.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, Ring.mul_inverse_cancel _ hM11, Matrix.one_mul]
  rw [blockSchur, blockSchur, hPM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  have hmid : (PL.toBlocks₂₁ * Mm.toBlocks₁₁ + Mm.toBlocks₂₁)
        * Ring.inverse (PL.toBlocks₁₁ * Mm.toBlocks₁₁) * (PL.toBlocks₁₁ * Mm.toBlocks₁₂)
      = PL.toBlocks₂₁ * Mm.toBlocks₁₂ + Mm.toBlocks₂₁ * Ring.inverse Mm.toBlocks₁₁ * Mm.toBlocks₁₂ := by
    rw [Matrix.mul_assoc _ (Ring.inverse (PL.toBlocks₁₁ * Mm.toBlocks₁₁)) (PL.toBlocks₁₁ * Mm.toBlocks₁₂),
      ← Matrix.mul_assoc (Ring.inverse (PL.toBlocks₁₁ * Mm.toBlocks₁₁)) PL.toBlocks₁₁ Mm.toBlocks₁₂,
      leftFrame_ringInverse_cancel PL.toBlocks₁₁ Mm.toBlocks₁₁ hPl11 hM11, Matrix.add_mul,
      Matrix.mul_assoc PL.toBlocks₂₁ Mm.toBlocks₁₁ (Ring.inverse Mm.toBlocks₁₁ * Mm.toBlocks₁₂),
      hMcancel, ← Matrix.mul_assoc Mm.toBlocks₂₁ (Ring.inverse Mm.toBlocks₁₁) Mm.toBlocks₁₂]
  rw [hmid]
  abel

/-- **A block-upper right frame is `blockSchur`-invisible.** With `QU.toBlocks₂₁ = 0`, `QU.toBlocks₂₂ = 1`
and units on `QU.toBlocks₁₁`, `M.toBlocks₁₁`, `blockSchur (M * QU) = blockSchur M`. -/
theorem blockSchur_upperFrame_of_blocks {σ τ : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ]
    (Mm : Matrix (ρ ⊕ σ) (ρ ⊕ τ) ℝ) (QU : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ)
    (hQu21 : QU.toBlocks₂₁ = 0) (hQu22 : QU.toBlocks₂₂ = 1)
    (hQu11 : IsUnit QU.toBlocks₁₁) (hM11 : IsUnit Mm.toBlocks₁₁) :
    blockSchur (Mm * QU) = blockSchur Mm := by
  have hMQ : Mm * QU = Matrix.fromBlocks (Mm.toBlocks₁₁ * QU.toBlocks₁₁)
      (Mm.toBlocks₁₁ * QU.toBlocks₁₂ + Mm.toBlocks₁₂) (Mm.toBlocks₂₁ * QU.toBlocks₁₁)
      (Mm.toBlocks₂₁ * QU.toBlocks₁₂ + Mm.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Mm, ← Matrix.fromBlocks_toBlocks QU]
    rw [Matrix.fromBlocks_multiply, hQu21, hQu22]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  rw [blockSchur, blockSchur, hMQ, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  have hmid : Mm.toBlocks₂₁ * QU.toBlocks₁₁ * Ring.inverse (Mm.toBlocks₁₁ * QU.toBlocks₁₁)
        * (Mm.toBlocks₁₁ * QU.toBlocks₁₂ + Mm.toBlocks₁₂)
      = Mm.toBlocks₂₁ * QU.toBlocks₁₂ + Mm.toBlocks₂₁ * Ring.inverse Mm.toBlocks₁₁ * Mm.toBlocks₁₂ := by
    rw [Matrix.mul_assoc Mm.toBlocks₂₁ QU.toBlocks₁₁ (Ring.inverse (Mm.toBlocks₁₁ * QU.toBlocks₁₁)),
      rightFrame_ringInverse_cancel QU.toBlocks₁₁ Mm.toBlocks₁₁ hQu11 hM11, Matrix.mul_add,
      ← Matrix.mul_assoc (Mm.toBlocks₂₁ * Ring.inverse Mm.toBlocks₁₁) Mm.toBlocks₁₁ QU.toBlocks₁₂,
      Matrix.mul_assoc Mm.toBlocks₂₁ (Ring.inverse Mm.toBlocks₁₁) Mm.toBlocks₁₁,
      Ring.inverse_mul_cancel _ hM11, Matrix.mul_one]
  rw [hmid]
  abel

/-- The frame telescope, prefix: `partProd Cf k = PL · partProd Cd k` for `1 ≤ k ≤ M` (the left frame at
layer `0` propagates through the interior layers, where `Cf = Cd`). -/
theorem partProd_frame_pre (Cd Cf : (s : ℕ) → Matrix (ρ ⊕ m s) (ρ ⊕ m (s + 1)) ℝ) (M : ℕ)
    (PL : Matrix (ρ ⊕ m 0) (ρ ⊕ m 0) ℝ) (hCf0 : Cf 0 = PL * Cd 0)
    (hInt : ∀ k, 1 ≤ k → k < M → Cf k = Cd k) :
    ∀ k, 1 ≤ k → k ≤ M → partProd Cf k = PL * partProd Cd k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hkM
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [show partProd Cf 1 = partProd Cf 0 * Cf 0 from rfl, show partProd Cf 0 = 1 from rfl,
        Matrix.one_mul, hCf0, show partProd Cd 1 = partProd Cd 0 * Cd 0 from rfl,
        show partProd Cd 0 = 1 from rfl, Matrix.one_mul]
    · rw [show partProd Cf (n + 1) = partProd Cf n * Cf n from rfl,
        ih hnpos (by omega), hInt n hnpos (by omega),
        show partProd Cd (n + 1) = partProd Cd n * Cd n from rfl, Matrix.mul_assoc]

/-- The frame telescope, last: `partProd Cf (M+1) = PL · partProd Cd (M+1) · QU` (adds the right frame at
the last layer `M`). -/
theorem partProd_frame_last (Cd Cf : (s : ℕ) → Matrix (ρ ⊕ m s) (ρ ⊕ m (s + 1)) ℝ) (M : ℕ) (hM : 1 ≤ M)
    (PL : Matrix (ρ ⊕ m 0) (ρ ⊕ m 0) ℝ) (QU : Matrix (ρ ⊕ m (M + 1)) (ρ ⊕ m (M + 1)) ℝ)
    (hCf0 : Cf 0 = PL * Cd 0) (hInt : ∀ k, 1 ≤ k → k < M → Cf k = Cd k)
    (hLast : Cf M = Cd M * QU) :
    partProd Cf (M + 1) = PL * partProd Cd (M + 1) * QU := by
  have hpre := partProd_frame_pre Cd Cf M PL hCf0 hInt M hM le_rfl
  rw [show partProd Cf (M + 1) = partProd Cf M * Cf M from rfl, hpre, hLast,
    show partProd Cd (M + 1) = partProd Cd M * Cd M from rfl]
  simp only [Matrix.mul_assoc]

/-- **Endpoint frames preserve `Kcoup`** (the core-side `regBlocks_movedC` analogue). A block-lower frame
`PL` at layer `0` and a block-upper frame `QU` at the last layer `M` (each identity `₂₂`-block, unit
`₁₁`-corner) leave every off-pivot coupling unchanged: `Kcoup Cf s = Kcoup Cd s`. The partial products
telescope (`partProd_frame_pre`/`_last`); the `P11`/`Q11` factors cancel through `Kcoup`'s inverse
(`leftFrame_ringInverse_cancel` interior, `conj_ringInverse_cancel` last layer). -/
theorem Kcoup_frame_endpoints (Cd Cf : (s : ℕ) → Matrix (ρ ⊕ m s) (ρ ⊕ m (s + 1)) ℝ) (M : ℕ) (hM : 1 ≤ M)
    (PL : Matrix (ρ ⊕ m 0) (ρ ⊕ m 0) ℝ) (QU : Matrix (ρ ⊕ m (M + 1)) (ρ ⊕ m (M + 1)) ℝ)
    (hPl12 : PL.toBlocks₁₂ = 0) (hPl11 : IsUnit PL.toBlocks₁₁)
    (hQu21 : QU.toBlocks₂₁ = 0) (hQu11 : IsUnit QU.toBlocks₁₁)
    (hCf0 : Cf 0 = PL * Cd 0) (hInt : ∀ k, 1 ≤ k → k < M → Cf k = Cd k) (hLast : Cf M = Cd M * QU)
    (hPd : ∀ k, IsUnit (partProd Cd k).toBlocks₁₁) (s : ℕ) (hs : s < M + 1) :
    Kcoup Cf s = Kcoup Cd s := by
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0; rw [Kcoup_zero, Kcoup_zero]
  · by_cases hslast : s = M
    · -- last layer `s = M`: both endpoint frames enter; `conj_ringInverse_cancel`.
      subst hslast
      have hcf21 : (Cf s).toBlocks₂₁ = (Cd s).toBlocks₂₁ * QU.toBlocks₁₁ := by
        rw [hLast, toBlocks₂₁_mul, hQu21, Matrix.mul_zero, add_zero]
      have hppS11 : (partProd Cf (s + 1)).toBlocks₁₁
          = PL.toBlocks₁₁ * (partProd Cd (s + 1)).toBlocks₁₁ * QU.toBlocks₁₁ := by
        rw [partProd_frame_last Cd Cf s hM PL QU hCf0 hInt hLast, toBlocks₁₁_mul, hQu21,
          Matrix.mul_zero, add_zero, toBlocks₁₁_mul, hPl12, Matrix.zero_mul, add_zero]
      have hpp12 : (partProd Cf s).toBlocks₁₂ = PL.toBlocks₁₁ * (partProd Cd s).toBlocks₁₂ := by
        rw [partProd_frame_pre Cd Cf s PL hCf0 hInt s hspos le_rfl, toBlocks₁₂_mul, hPl12,
          Matrix.zero_mul, add_zero]
      rw [Kcoup, Kcoup, hcf21, hppS11, hpp12,
        ← conj_ringInverse_cancel PL.toBlocks₁₁ (partProd Cd (s + 1)).toBlocks₁₁ QU.toBlocks₁₁
          hPl11 (hPd (s + 1)) hQu11]
      simp only [Matrix.mul_assoc]
    · -- interior layer `1 ≤ s < M`: only the left frame enters; `leftFrame_ringInverse_cancel`.
      have hsltM : s < M := lt_of_le_of_ne (by omega) hslast
      have hppS11 : (partProd Cf (s + 1)).toBlocks₁₁
          = PL.toBlocks₁₁ * (partProd Cd (s + 1)).toBlocks₁₁ := by
        rw [partProd_frame_pre Cd Cf M PL hCf0 hInt (s + 1) (by omega) (by omega), toBlocks₁₁_mul,
          hPl12, Matrix.zero_mul, add_zero]
      have hpp12 : (partProd Cf s).toBlocks₁₂ = PL.toBlocks₁₁ * (partProd Cd s).toBlocks₁₂ := by
        rw [partProd_frame_pre Cd Cf M PL hCf0 hInt s hspos (by omega), toBlocks₁₂_mul, hPl12,
          Matrix.zero_mul, add_zero]
      rw [Kcoup, Kcoup, hInt s hspos hsltM, hppS11, hpp12,
        ← leftFrame_ringInverse_cancel PL.toBlocks₁₁ (partProd Cd (s + 1)).toBlocks₁₁ hPl11 (hPd (s + 1))]
      simp only [Matrix.mul_assoc]

end AbstractFrame

/-! ## Lemma 3 — the interior framed chain equals the decode chain

At a strict-interior layer both gauge frames are trivial (`Pf s = Qf s = 1`), so
`framedParamsPivot … (split x) s = (decode x) s` (`framedParamsPivot_eq_frame_of_front`), and the two
`deepestChain` layers coincide. -/

/-- **Interior framed = decode chain.** For interior `s`, the framed chain of `split x` and the decode
chain of `x` agree at layer `s`. -/
theorem deepestChain_framed_eq_decode_interior (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (J : Fin r ↪ Fin (H (Fin.last L)))
    (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
      Pf s * (deepestPoint H r B hB hr hL s) * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hPfL : Pf (lastLayer hL)
      = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hcorner : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hInterior : ∀ s : Fin L, 0 < (s : ℕ) → (s : ℕ) + 1 < L → Pf s = 1 ∧ Qf s = 1)
    (x : Fin (flatDim H) → ℝ) (s : Fin L) (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L) :
    deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x)) (s : ℕ)
      = deepestChain H r hr ((paramsEquivFlat H).symm x) (s : ℕ) := by
  have hframe := framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront Pf Qf hNF hPfL hcorner x s
  obtain ⟨hP1, hQ1⟩ := hInterior s hpos hlt
  rw [hP1, hQ1, Matrix.one_mul, Matrix.mul_one] at hframe
  rw [deepestChain, deepestChain, deepestChainLayer, deepestChainLayer, dif_pos s.isLt, dif_pos s.isLt,
    show framedParamsPivot H r hr hL J Pf Qf
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x)
        ⟨(s : ℕ), s.isLt⟩ = ((paramsEquivFlat H).symm x) ⟨(s : ℕ), s.isLt⟩ from hframe]

end DLNFibre.DLN.RLCT
