import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGenMove
import DLNFibre.DLN.RLCT.Validate.DeepestFramedBoundaryMove

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedBoundaryDecode` — the boundary framed-chain decode (#120 item 1)

The FRAME-DEPENDENT boundary analog of the interior `deepestChain_framedParamsPivot_blocks_of_frame_one`
(`DeepestFramedChainDecode`). For the two boundary layers (`firstLayer`, `lastLayer`) the gauge frames
`Pf firstLayer` / `Qf lastLayer` are NOT the identity (they are block-triangular with identity `₂₂`-block,
from the triangular bundle `DeepestPivotFrameTriangular`), so the frame-trivial collapse does not apply.

This module keeps the frame explicit and, combined with the banked forced-decode identities
(`fromBlocks_lowerFrame_mul_forcedDecode` / `_rightUpper_`, `DeepestFramedBoundaryMove`), proves the two
boundary halves of the move identity `hmove`:

* `psiSplitRawGen_deepestChain_firstLayer` — `deepestChain (framedParamsPivot (psiSplitRawGen q)) 0 =
  movedC (deepestChain (framedParamsPivot q)) (Z0edit0 …) 0`, via `psiGhat q firstLayer =
  forcedDecodeLeft psiFrame0 (movedC 0 − corM)` and the block-LOWER frame move.
* `psiSplitRawGen_deepestChain_lastLayer` — the symmetric last-layer half via the block-UPPER frame move
  (with the `J = frontEmbed` pivot→threshold collapse).

Pure `Matrix`/`Equiv` reindex algebra over `ℝ`. The frame-corner invertibility enters through the bundle
units (`hPf`/`hQf` + the block-triangular `₂₂ = 1` facts ⟹ the `₁₁` corner is a unit).
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-- **Frame–reindex commutation.** Pulling a square left frame `P` through a reindexed matrix: with the
row/column relabels `e`, `f`, `P · reindex e.symm f.symm N = reindex e.symm f.symm (reindex e e P · N)`.
The frame is transported into the split coordinates by `reindex e e`; the shared middle index cancels via
`submatrix_mul_equiv`. -/
theorem frame_mul_reindex {n p ρ σ : Type*} [Fintype n] [Fintype ρ]
    (e : n ≃ ρ) (f : p ≃ σ) (P : Matrix n n ℝ) (N : Matrix ρ σ ℝ) :
    P * Matrix.reindex e.symm f.symm N
      = Matrix.reindex e.symm f.symm (Matrix.reindex e e P * N) := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [← Matrix.submatrix_mul_equiv (Matrix.submatrix P e.symm e.symm) N e e f,
    Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

/-- **Reindex of a product splits at a chosen middle relabel.** `reindex e g (P · M) = reindex e mid P ·
reindex mid g M` — the contracted index is relabelled by `mid`. Pure `submatrix_mul_equiv`. -/
theorem reindex_mul {ι α κ ι' α' κ' : Type*} [Fintype α] [Fintype α']
    (e : ι ≃ ι') (mid : α ≃ α') (g : κ ≃ κ') (P : Matrix ι α ℝ) (M : Matrix α κ ℝ) :
    Matrix.reindex e g (P * M) = Matrix.reindex e mid P * Matrix.reindex mid g M := by
  simp only [Matrix.reindex_apply]
  exact (Matrix.submatrix_mul_equiv P M e.symm mid.symm g.symm).symm

/-! ## The chain-width reindex of a threshold `fromBlocks` (whole-matrix, reusable) -/

/-- **Chain-width reindex of a threshold `fromBlocks`.** For any interior layer `s`, applying the
`deepestChain` reindex chain (`deepestChainSplit ∘ finCongr ∘ (rThresholdSplit).symm`) to a threshold-split
`fromBlocks A B C D` relabels it into chain-block form: `fromBlocks A (reindex .. B) (reindex .. C)
(reindex .. D)`, with the reduced-width `finCongr` relabels matching the read round-trips
(`chainWidth_succ_sub`/`chainWidth_castSucc_sub`). The whole-matrix analog of the interior block decode. -/
theorem reindexChain_fromBlocks (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : Fin L)
    (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin (H s.succ - r)) ℝ)
    (C : Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
    (D : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ) :
    Matrix.reindex (deepestChainSplit H r hr (s : ℕ)) (deepestChainSplit H r hr ((s : ℕ) + 1))
        (Matrix.reindex (finCongr (deepestChainWidth_castSucc H (s : ℕ) s.isLt))
            (finCongr (deepestChainWidth_succ H (s : ℕ) s.isLt))
          (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
              (rThresholdSplit r (H s.succ) (hr s.succ)).symm
            (Matrix.fromBlocks A B C D)))
      = Matrix.fromBlocks A
          (Matrix.reindex (Equiv.refl (Fin r)) (finCongr (chainWidth_succ_sub H r s)) B)
          (Matrix.reindex (finCongr (chainWidth_castSucc_sub H r s)) (Equiv.refl (Fin r)) C)
          (Matrix.reindex (finCongr (chainWidth_castSucc_sub H r s))
            (finCongr (chainWidth_succ_sub H r s)) D) := by
  funext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.refl_symm,
    deepestChainSplit]
  rcases i with i | i <;> rcases j with j | j
  · rw [rThr_finCongr_split_inl r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inl r _ _ (deepestChainWidth_succ H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₁]
  · rw [rThr_finCongr_split_inl r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inr r _ _ (deepestChainWidth_succ H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₁₂]
    simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_apply, Fin.cast_eq_cast]
  · rw [rThr_finCongr_split_inr r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inl r _ _ (deepestChainWidth_succ H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₁]
    simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_apply, Fin.cast_eq_cast]
  · rw [rThr_finCongr_split_inr r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inr r _ _ (deepestChainWidth_succ H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₂]
    simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_apply, Fin.cast_eq_cast]

/-- **Square chain-width reindex of a threshold `fromBlocks`** (castSucc–castSucc, for the layer-0 frame
`psiFrame0`). Same as `reindexChain_fromBlocks` but with the castSucc widths on both sides. -/
theorem reindexChainSq_fromBlocks (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : Fin L)
    (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin (H s.castSucc - r)) ℝ)
    (C : Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
    (D : Matrix (Fin (H s.castSucc - r)) (Fin (H s.castSucc - r)) ℝ) :
    Matrix.reindex (deepestChainSplit H r hr (s : ℕ)) (deepestChainSplit H r hr (s : ℕ))
        (Matrix.reindex (finCongr (deepestChainWidth_castSucc H (s : ℕ) s.isLt))
            (finCongr (deepestChainWidth_castSucc H (s : ℕ) s.isLt))
          (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
              (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
            (Matrix.fromBlocks A B C D)))
      = Matrix.fromBlocks A
          (Matrix.reindex (Equiv.refl (Fin r)) (finCongr (chainWidth_castSucc_sub H r s)) B)
          (Matrix.reindex (finCongr (chainWidth_castSucc_sub H r s)) (Equiv.refl (Fin r)) C)
          (Matrix.reindex (finCongr (chainWidth_castSucc_sub H r s))
            (finCongr (chainWidth_castSucc_sub H r s)) D) := by
  funext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.refl_symm,
    deepestChainSplit]
  rcases i with i | i <;> rcases j with j | j
  · rw [rThr_finCongr_split_inl r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inl r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₁]
  · rw [rThr_finCongr_split_inl r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inr r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₁₂]
    simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_apply, Fin.cast_eq_cast]
  · rw [rThr_finCongr_split_inr r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inl r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₁]
    simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_apply, Fin.cast_eq_cast]
  · rw [rThr_finCongr_split_inr r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inr r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₂]
    simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_apply, Fin.cast_eq_cast]

/-! ## Step A — the H-width frame-KEEPING layer expansion (firstLayer, `Qf = 1`) -/

/-- **Frame-keeping firstLayer expansion.** For the first layer (which is not the pivot-carrying last
layer, `2 ≤ L`), with a trivial right frame `Qf firstLayer = 1`, `framedParamsPivot` degenerates to the
frame-shifted additive chart `reindex (rThr.symm) (rThr.symm) (corM + Pt · fromBlocks X Y Z T)`, where
`Pt := reindex (rThr) (rThr) (Pf firstLayer)` is the layer-0 frame in threshold-block form and
`(X, Y, Z, T)` are the gauge/core reads. The `P = 1` case is `framedParamsPivot_frame_one_eq`. -/
theorem framedParamsPivot_frame_firstLayer_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (hQ : Qf (firstLayer hL) = 1) :
    framedParamsPivot H r hr hL J Pf Qf q (firstLayer hL)
      = Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
          (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
            + (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
                (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)) (Pf (firstLayer hL)))
              * Matrix.fromBlocks (gaugeReadX H r hr hL (q.1, q.2.2) (firstLayer hL))
                (gaugeReadY H r hr hL (q.1, q.2.2) (firstLayer hL))
                (gaugeReadZ H r hr hL (q.1, q.2.2) (firstLayer hL))
                ((paramsEquivFlat (deepestM H r)).symm q.2.1 (firstLayer hL))) := by
  have hfne : firstLayer hL ≠ lastLayer hL := by
    intro h; have := congrArg Fin.val h; simp only [firstLayer, lastLayer] at this; omega
  rw [framedParamsPivot_of_ne_last H r hr hL J Pf Qf q (firstLayer hL) hfne, framedParams,
    framedLayer, hQ, Matrix.mul_one,
    frame_mul_reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
      (rThresholdSplit r (H (firstLayer hL).succ) (hr _)) (Pf (firstLayer hL))
      (Matrix.fromBlocks (gaugeReadX H r hr hL (q.1, q.2.2) (firstLayer hL))
        (gaugeReadY H r hr hL (q.1, q.2.2) (firstLayer hL))
        (gaugeReadZ H r hr hL (q.1, q.2.2) (firstLayer hL))
        ((paramsEquivFlat (deepestM H r)).symm q.2.1 (firstLayer hL)))]
  simp only [Matrix.reindex_apply]
  rfl

/-! ## Step B — the firstLayer chain-width decode -/

/-- **firstLayer chain-width decode.** The abstract chain layer of `framedParamsPivot q` at the first
layer decodes into `corM + psiFrame0 · (chain-block reads)`: the additive corner plus the layer-0 frame
(`psiFrame0`) times the chain-width `fromBlocks` of the gauge/core reads (in the reduced-width relabels
matching the read round-trips). Whole-matrix: `reindexChain_fromBlocks` handles the corner and the reads,
`reindex_mul` factors the frame. -/
theorem deepestChain_framedParamsPivot_firstLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (hQ : Qf (firstLayer hL) = 1) :
    deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (firstLayer hL : ℕ)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + psiFrame0 H r hr hL Pf
          * Matrix.fromBlocks (gaugeReadX H r hr hL (q.1, q.2.2) (firstLayer hL))
              (Matrix.reindex (Equiv.refl (Fin r)) (finCongr (chainWidth_succ_sub H r (firstLayer hL)))
                (gaugeReadY H r hr hL (q.1, q.2.2) (firstLayer hL)))
              (Matrix.reindex (finCongr (chainWidth_castSucc_sub H r (firstLayer hL)))
                (Equiv.refl (Fin r)) (gaugeReadZ H r hr hL (q.1, q.2.2) (firstLayer hL)))
              (Matrix.reindex (finCongr (chainWidth_castSucc_sub H r (firstLayer hL)))
                (finCongr (chainWidth_succ_sub H r (firstLayer hL)))
                ((paramsEquivFlat (deepestM H r)).symm q.2.1 (firstLayer hL))) := by
  rw [deepestChain, deepestChainLayer, dif_pos (firstLayer hL).isLt,
    show (framedParamsPivot H r hr hL J Pf Qf q ⟨(firstLayer hL : ℕ), (firstLayer hL).isLt⟩)
        = framedParamsPivot H r hr hL J Pf Qf q (firstLayer hL) from rfl,
    framedParamsPivot_frame_firstLayer_eq H r hr hL hL2 J Pf Qf q hQ]
  set Pt := Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
      (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)) (Pf (firstLayer hL)) with hPt
  set FBr := Matrix.fromBlocks (gaugeReadX H r hr hL (q.1, q.2.2) (firstLayer hL))
      (gaugeReadY H r hr hL (q.1, q.2.2) (firstLayer hL))
      (gaugeReadZ H r hr hL (q.1, q.2.2) (firstLayer hL))
      ((paramsEquivFlat (deepestM H r)).symm q.2.1 (firstLayer hL)) with hFBr
  -- Additivity of the reindex chain: split `corM + frame·reads`.
  have hadd : Matrix.reindex (deepestChainSplit H r hr (firstLayer hL : ℕ))
        (deepestChainSplit H r hr ((firstLayer hL : ℕ) + 1))
        (Matrix.reindex (finCongr (deepestChainWidth_castSucc H (firstLayer hL : ℕ) (firstLayer hL).isLt))
          (finCongr (deepestChainWidth_succ H (firstLayer hL : ℕ) (firstLayer hL).isLt))
          (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
              (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + Pt * FBr)))
      = Matrix.reindex (deepestChainSplit H r hr (firstLayer hL : ℕ))
          (deepestChainSplit H r hr ((firstLayer hL : ℕ) + 1))
          (Matrix.reindex (finCongr (deepestChainWidth_castSucc H (firstLayer hL : ℕ) (firstLayer hL).isLt))
            (finCongr (deepestChainWidth_succ H (firstLayer hL : ℕ) (firstLayer hL).isLt))
            (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
                (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm
              (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)))
        + Matrix.reindex (deepestChainSplit H r hr (firstLayer hL : ℕ))
            (deepestChainSplit H r hr ((firstLayer hL : ℕ) + 1))
            (Matrix.reindex (finCongr (deepestChainWidth_castSucc H (firstLayer hL : ℕ) (firstLayer hL).isLt))
              (finCongr (deepestChainWidth_succ H (firstLayer hL : ℕ) (firstLayer hL).isLt))
              (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
                  (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm (Pt * FBr))) := by
    funext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
  rw [hadd]
  congr 1
  · -- corM part: `reindexChain (fromBlocks 1 0 0 0) = fromBlocks 1 0 0 0`.
    rw [reindexChain_fromBlocks H r hr (firstLayer hL) (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0]
    simp
  · -- product part: `reindexChain (Pt * FBr) = psiFrame0 * (chain-block reads)`.
    rw [reindex_mul (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
          (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
          (rThresholdSplit r (H (firstLayer hL).succ) (hr _)).symm Pt FBr,
        reindex_mul (finCongr (deepestChainWidth_castSucc H (firstLayer hL : ℕ) (firstLayer hL).isLt))
          (finCongr (deepestChainWidth_castSucc H (firstLayer hL : ℕ) (firstLayer hL).isLt))
          (finCongr (deepestChainWidth_succ H (firstLayer hL : ℕ) (firstLayer hL).isLt)) _ _,
        reindex_mul (deepestChainSplit H r hr (firstLayer hL : ℕ))
          (deepestChainSplit H r hr (firstLayer hL : ℕ))
          (deepestChainSplit H r hr ((firstLayer hL : ℕ) + 1)) _ _]
    congr 1
    · -- `reindexChainSq Pt = psiFrame0`.
      rw [hPt, psiFrame0]
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_symm,
        Equiv.symm_comp_self, Matrix.submatrix_id_id]
    · -- `reindexChain FBr = chain-block reads` (`reindexChain_fromBlocks`).
      rw [hFBr]
      exact reindexChain_fromBlocks H r hr (firstLayer hL)
        (gaugeReadX H r hr hL (q.1, q.2.2) (firstLayer hL))
        (gaugeReadY H r hr hL (q.1, q.2.2) (firstLayer hL))
        (gaugeReadZ H r hr hL (q.1, q.2.2) (firstLayer hL))
        ((paramsEquivFlat (deepestM H r)).symm q.2.1 (firstLayer hL))

/-! ## The firstLayer boundary move identity -/

/-- **Block-lower frame move (`toBlocks` form).** For a block-lower `M` (`M₁₂ = 0`, `M₂₂ = 1`, `M₁₁` a
right-unit under `Ring.inverse`), `M · forcedDecodeLeft M D = D`. Wraps `fromBlocks_lowerFrame_mul_forcedDecode`. -/
theorem blockLower_mul_forcedDecodeLeft {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (M : Matrix (r ⊕ a) (r ⊕ a) ℝ) (D : Matrix (r ⊕ a) (r ⊕ b) ℝ)
    (h12 : M.toBlocks₁₂ = 0) (h22 : M.toBlocks₂₂ = 1)
    (hunit : M.toBlocks₁₁ * Ring.inverse M.toBlocks₁₁ = 1) :
    M * forcedDecodeLeft M D = D := by
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 1 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h12, h22]
  rw [forcedDecodeLeft]
  nth_rewrite 1 [hM]
  rw [fromBlocks_lowerFrame_mul_forcedDecode M.toBlocks₁₁ (Ring.inverse M.toBlocks₁₁) M.toBlocks₂₁
      D.toBlocks₁₁ D.toBlocks₁₂ D.toBlocks₂₁ D.toBlocks₂₂ hunit, Matrix.fromBlocks_toBlocks]

/-- `psiGhat q firstLayer = forcedDecodeLeft psiFrame0 (psiTargetD q firstLayer)` (the def's first-layer
branch; the `▸` cast is trivial by proof irrelevance of `firstLayer = firstLayer`). -/
theorem psiGhat_firstLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    psiGhat H r hr hL J Pf Qf q (firstLayer hL)
      = forcedDecodeLeft (psiFrame0 H r hr hL Pf)
          (psiTargetD H r hr hL J Pf Qf q (firstLayer hL : ℕ)) := by
  have hfne : firstLayer hL ≠ lastLayer hL := by
    intro h; have := congrArg Fin.val h; simp only [firstLayer, lastLayer] at this; omega
  rw [psiGhat, dif_neg hfne, dif_pos rfl]

/-- **The firstLayer boundary move identity.** `deepestChain (framedParamsPivot (psiSplitRawGen q)) 0 =
movedC (deepestChain (framedParamsPivot q)) (Z0edit0 …) 0`. The chain decode gives `corM + psiFrame0 ·
psiGhat`; `psiGhat = forcedDecodeLeft psiFrame0 (movedC − corM)` and the block-LOWER frame move collapse
`psiFrame0 · forcedDecodeLeft psiFrame0 D = D`, then `corM + (movedC − corM) = movedC`. -/
theorem psiSplitRawGen_deepestChain_firstLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (hQ : Qf (firstLayer hL) = 1)
    (hPunit : IsUnit (Pf (firstLayer hL)))
    (hPtri : (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (Pf (firstLayer hL))).toBlocks₁₂ = 0)
    (hP22 : (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (Pf (firstLayer hL))).toBlocks₂₂ = 1) :
    deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf (psiSplitRawGen H r hr hL J Pf Qf q))
        (firstLayer hL : ℕ)
      = movedC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L)
          (firstLayer hL : ℕ) := by
  -- The layer-0 frame `Pt` in threshold-block form + its block-lower structure.
  set Pt := Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
      (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)) (Pf (firstLayer hL)) with hPtdef
  -- `psiFrame0` is block-lower with the same `₁₁`/`₂₁` blocks (transported to chain width).
  have hpf0 : psiFrame0 H r hr hL Pf
      = Matrix.fromBlocks Pt.toBlocks₁₁ 0
          (Matrix.reindex (finCongr (chainWidth_castSucc_sub H r (firstLayer hL))) (Equiv.refl (Fin r))
            Pt.toBlocks₂₁) 1 := by
    have hPtlow : Pt = Matrix.fromBlocks Pt.toBlocks₁₁ 0 Pt.toBlocks₂₁ 1 := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks Pt]
      rw [hPtri, hP22]
    have hPf_eq : Pf (firstLayer hL)
        = Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm
            (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)).symm Pt := by
      rw [hPtdef, ← Matrix.reindex_symm]
      exact ((Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
        (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))).symm_apply_apply _).symm
    rw [psiFrame0, hPf_eq]
    nth_rewrite 1 [hPtlow]
    rw [reindexChainSq_fromBlocks H r hr (firstLayer hL) Pt.toBlocks₁₁ 0 Pt.toBlocks₂₁ 1]
    simp
  have h12 : (psiFrame0 H r hr hL Pf).toBlocks₁₂ = 0 := by
    rw [hpf0, Matrix.toBlocks_fromBlocks₁₂]
  have h22 : (psiFrame0 H r hr hL Pf).toBlocks₂₂ = 1 := by
    rw [hpf0, Matrix.toBlocks_fromBlocks₂₂]
  have hpsiunit : IsUnit (psiFrame0 H r hr hL Pf) := by
    rw [psiFrame0]
    simp only [Matrix.reindex_apply]
    exact (Matrix.isUnit_submatrix_equiv _ _).mpr ((Matrix.isUnit_submatrix_equiv _ _).mpr hPunit)
  have hunit : IsUnit (psiFrame0 H r hr hL Pf).toBlocks₁₁ := by
    have hdet : (psiFrame0 H r hr hL Pf).det = (psiFrame0 H r hr hL Pf).toBlocks₁₁.det := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (psiFrame0 H r hr hL Pf)]
      rw [h12, h22, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [← hdet]; exact (Matrix.isUnit_iff_isUnit_det _).mp hpsiunit
  -- The chain decode + read round-trips + `psiGhat` first-layer branch.
  rw [deepestChain_framedParamsPivot_firstLayer H r hr hL hL2 J Pf Qf
      (psiSplitRawGen H r hr hL J Pf Qf q) hQ,
    gaugeReadX_psiSplitRawGen_eq_psiGhat, gaugeReadY_psiSplitRawGen_eq_psiGhat,
    gaugeReadZ_psiSplitRawGen_eq_psiGhat, coreRead_psiSplitRawGen_eq_psiGhat,
    Matrix.fromBlocks_toBlocks, psiGhat_firstLayer H r hr hL hL2 J Pf Qf q,
    blockLower_mul_forcedDecodeLeft (psiFrame0 H r hr hL Pf)
      (psiTargetD H r hr hL J Pf Qf q (firstLayer hL : ℕ)) h12 h22
      (Ring.mul_inverse_cancel _ hunit),
    psiTargetD]
  abel

end DLNFibre.DLN.RLCT
