import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGenMove
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback
import DLNFibre.DLN.RLCT.Validate.DeepestHmoveGen
import DLNFibre.DLN.RLCT.Validate.DeepestDeepBlkBoundaryGen
import DLNFibre.DLN.RLCT.Validate.DeepestHsub4coreInvGerm

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

/-! ## Interior-layer deepest-block vanishing (`deepBlkZ`, `deepBlkT`) -/

/-- **Interior deepest layers vanish at rows `≥ r`** (rows-mirror of the banked cols version): the
interior corner `diag(I_r, 0)` (`deepestPoint_interior_eq_corM`) is `0` at any row `≥ r`. -/
theorem deepestPoint_interior_rows_vanish (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L)
    (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) (hi : r ≤ (i : ℕ)) :
    deepestPoint H r B hB hr hL s i j = 0 := by
  rw [deepestPoint_interior_eq_corM H r B hB hr hL s hpos hlt]
  simp only [Matrix.of_apply]
  rw [if_neg]
  rintro ⟨_, h⟩
  omega

/-- **`deepBlkZ_s = 0` at interior layers.** `toBlocks₂₁` reads rows `≥ r`, where the interior
corner is `0` (`deepestPoint_interior_rows_vanish`). Mirror of `deepBlkY_interior_zero` on rows. -/
theorem deepBlkZ_interior_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L) :
    deepBlkZ H r B hB hr hL s = 0 := by
  funext i j
  change (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inl j)) = 0
  rw [rThresholdSplit_symm_inr]
  exact deepestPoint_interior_rows_vanish H r B hB hr hL s hpos hlt _ _ (by simp)

/-- **`deepBlkT_s = 0` at interior layers** (`(reindex deepest)_s.toBlocks₂₂ = 0`): `toBlocks₂₂`
reads rows `≥ r`, killed by the interior corner (`deepestPoint_interior_rows_vanish`). -/
theorem deepBlkT_interior_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (hpos : 0 < (s : ℕ)) (hlt : (s : ℕ) + 1 < L) :
    (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0 := by
  funext i j
  change (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr j)) = 0
  rw [rThresholdSplit_symm_inr]
  exact deepestPoint_interior_rows_vanish H r B hB hr hL s hpos hlt _ _ (by simp)

end DLNFibre.DLN.RLCT
