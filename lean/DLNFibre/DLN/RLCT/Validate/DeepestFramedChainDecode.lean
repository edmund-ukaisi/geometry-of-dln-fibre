import DLNFibre.DLN.RLCT.Validate.DeepestFinBridgeGen
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProductPivot

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedChainDecode` — interior framed-chain block decode (#120 item 2)

The frame-trivial (interior) half of the per-layer readback that item 2 of the `hstep2` build order needs
(germs7: "no framed-chain block decode exists yet"). For a layer `s` whose gauge frames are trivial
(`Pf s = 1`, `Qf s = 1`) and which is not the pivot-carrying last layer (`s ≠ lastLayer`),
`framedParamsPivot` degenerates to the additive threshold chart `corM + reindex (fromBlocks X Y Z T)`, so
the abstract chain layer `deepestChain (framedParamsPivot … q) s` decodes into its four residual blocks
directly:

* `toBlocks₁₁ = 1 + gaugeReadX`,
* `toBlocks₁₂ = gaugeReadY` (reduced-width relabel),
* `toBlocks₂₁ = gaugeReadZ` (reduced-width relabel),
* `toBlocks₂₂ = (paramsEquivFlat (deepestM)).symm q.2.1 s` (the core read, reduced-width relabel).

This is the interior collapse of `hmove`'s `funext s; by_cases s < L`; the boundary layers (0/last) use the
banked `DeepestFramedBoundaryMove` forced-decode identities instead. Pure `Matrix`/`Equiv` algebra over `ℝ`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-- The interior reduced-width bridge: `H s.castSucc - r = deepestChainWidth H (s : ℕ) - r`. -/
theorem chainWidth_castSucc_sub (H : Fin (L + 1) → ℕ) (r : ℕ) (s : Fin L) :
    H s.castSucc - r = deepestChainWidth H (s : ℕ) - r := by
  rw [show H s.castSucc = H (⟨(s : ℕ), s.isLt⟩ : Fin L).castSucc from rfl,
    deepestChainWidth_castSucc H (s : ℕ) s.isLt]

/-- The interior reduced-width bridge: `H s.succ - r = deepestChainWidth H ((s : ℕ) + 1) - r`. -/
theorem chainWidth_succ_sub (H : Fin (L + 1) → ℕ) (r : ℕ) (s : Fin L) :
    H s.succ - r = deepestChainWidth H ((s : ℕ) + 1) - r := by
  rw [show H s.succ = H (⟨(s : ℕ), s.isLt⟩ : Fin L).succ from rfl,
    deepestChainWidth_succ H (s : ℕ) s.isLt]

/-- **The frame-trivial layer collapse.** On a layer with trivial frames (`Pf s = 1`, `Qf s = 1`) that is
not the pivot-carrying last layer, `framedParamsPivot` degenerates to the additive threshold chart:
`framedParamsPivot … q s = reindex (rThr.symm) (rThr.symm) (fromBlocks (1 + X) Y Z T)`, with `(X, Y, Z)`
the gauge reads and `T` the core read. -/
theorem framedParamsPivot_frame_one_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L)
    (hne : s ≠ lastLayer hL) (hP : Pf s = 1) (hQ : Qf s = 1) :
    framedParamsPivot H r hr hL J Pf Qf q s
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (1 + gaugeReadX H r hr hL (q.1, q.2.2) s)
            (gaugeReadY H r hr hL (q.1, q.2.2) s)
            (gaugeReadZ H r hr hL (q.1, q.2.2) s)
            ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)) := by
  have hblk : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.fromBlocks (gaugeReadX H r hr hL (q.1, q.2.2) s)
            (gaugeReadY H r hr hL (q.1, q.2.2) s) (gaugeReadZ H r hr hL (q.1, q.2.2) s)
            ((paramsEquivFlat (deepestM H r)).symm q.2.1 s))
      = Matrix.fromBlocks (1 + gaugeReadX H r hr hL (q.1, q.2.2) s)
          (gaugeReadY H r hr hL (q.1, q.2.2) s) (gaugeReadZ H r hr hL (q.1, q.2.2) s)
          ((paramsEquivFlat (deepestM H r)).symm q.2.1 s) := by
    rw [Matrix.fromBlocks_add]; simp only [zero_add]
  rw [framedParamsPivot_of_ne_last H r hr hL J Pf Qf q s hne, framedParams, framedLayer, hP, hQ,
    Matrix.one_mul, Matrix.mul_one, ← hblk]
  simp only [Matrix.reindex_apply]
  rfl

/-- Index image (`inl` side): the threshold split absorbs the `deepestChainSplit`/`finCongr` prefix on
the first `r` block. `rThr_a (finCongr.symm (rThr_b.symm (inl i))) = inl i` for equal widths `a = b`. -/
theorem rThr_finCongr_split_inl {a b : ℕ} (r : ℕ) (ha : r ≤ a) (hb : r ≤ b) (hab : a = b)
    (i : Fin r) :
    (rThresholdSplit r a ha) ((finCongr hab).symm ((rThresholdSplit r b hb).symm (Sum.inl i)))
      = Sum.inl i := by
  have harg : (finCongr hab).symm ((rThresholdSplit r b hb).symm (Sum.inl i)) = i.castLE ha := by
    rw [rThresholdSplit_symm_inl]; apply Fin.ext; simp [Fin.castLE, finCongr]
  rw [harg, ← rThresholdSplit_symm_inl r a ha i, Equiv.apply_symm_apply]

/-- Index image (`inr` side): on the reduced block the composite is the reduced-width relabel.
`rThr_a (finCongr.symm (rThr_b.symm (inr j))) = inr (Fin.cast j)`. -/
theorem rThr_finCongr_split_inr {a b : ℕ} (r : ℕ) (ha : r ≤ a) (hb : r ≤ b) (hab : a = b)
    (j : Fin (b - r)) :
    (rThresholdSplit r a ha) ((finCongr hab).symm ((rThresholdSplit r b hb).symm (Sum.inr j)))
      = Sum.inr (Fin.cast (by rw [hab]) j) := by
  have harg : (finCongr hab).symm ((rThresholdSplit r b hb).symm (Sum.inr j))
      = (rThresholdSplit r a ha).symm (Sum.inr (Fin.cast (by rw [hab]) j)) := by
    rw [rThresholdSplit_symm_inr, rThresholdSplit_symm_inr]
    apply Fin.ext; simp [finCongr, Fin.cast]
  rw [harg, Equiv.apply_symm_apply]

/-- **The interior framed-chain block decode.** For a frame-trivial layer (`Pf s = 1`, `Qf s = 1`) that is
not the pivot-carrying last layer, the abstract chain layer `deepestChain (framedParamsPivot … q) s`
decodes into the four gauge/core reads: pivot `1 + gaugeReadX`, up-block `gaugeReadY`, down-block
`gaugeReadZ`, core `(paramsEquivFlat (deepestM)).symm q.2.1 s` — each on the reduced-width relabel. This is
the interior collapse of `hmove`'s `funext s; by_cases s < L`. -/
theorem deepestChain_framedParamsPivot_blocks_of_frame_one (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L)
    (hne : s ≠ lastLayer hL) (hP : Pf s = 1) (hQ : Qf s = 1) :
    (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (s : ℕ)).toBlocks₁₁
        = 1 + gaugeReadX H r hr hL (q.1, q.2.2) s
      ∧ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (s : ℕ)).toBlocks₁₂
        = Matrix.reindex (Equiv.refl (Fin r)) (finCongr (chainWidth_succ_sub H r s))
            (gaugeReadY H r hr hL (q.1, q.2.2) s)
      ∧ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (s : ℕ)).toBlocks₂₁
        = Matrix.reindex (finCongr (chainWidth_castSucc_sub H r s)) (Equiv.refl (Fin r))
            (gaugeReadZ H r hr hL (q.1, q.2.2) s)
      ∧ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (s : ℕ)).toBlocks₂₂
        = Matrix.reindex (finCongr (chainWidth_castSucc_sub H r s))
            (finCongr (chainWidth_succ_sub H r s))
            ((paramsEquivFlat (deepestM H r)).symm q.2.1 s) := by
  -- shared: the layer as a threshold-reindex of `fromBlocks`.
  have hlayer := framedParamsPivot_frame_one_eq H r hr hL J Pf Qf q ⟨(s : ℕ), s.isLt⟩ hne hP hQ
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (funext i j
     simp only [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
       Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
       Equiv.refl_apply]
     rw [deepestChain]
     simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
     rw [deepestChainLayer, dif_pos s.isLt, hlayer]
     simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, deepestChainSplit])
  · rw [rThr_finCongr_split_inl r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inl r _ _ (deepestChainWidth_succ H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₁₁]
  · rw [rThr_finCongr_split_inl r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inr r _ _ (deepestChainWidth_succ H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₁₂]
    rfl
  · rw [rThr_finCongr_split_inr r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inl r _ _ (deepestChainWidth_succ H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₂₁]
    rfl
  · rw [rThr_finCongr_split_inr r _ _ (deepestChainWidth_castSucc H (s : ℕ) s.isLt) i,
      rThr_finCongr_split_inr r _ _ (deepestChainWidth_succ H (s : ℕ) s.isLt) j,
      Matrix.fromBlocks_apply₂₂]
    rfl

end DLNFibre.DLN.RLCT
