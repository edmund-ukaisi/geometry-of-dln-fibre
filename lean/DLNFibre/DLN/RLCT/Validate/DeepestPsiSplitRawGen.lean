import DLNFibre.DLN.RLCT.Validate.DeepestFramedChainDecode

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGen` — the general-`L` joint move `psiSplitRawGen`

Item 1 of the #120 `hstep2` build order (deferred across germs5-8). The concrete split-side joint
move `psiSplitRawGen : DeepestSplit → DeepestSplit` whose framed-chain image is the abstract moved
chain `movedC` — i.e. the object that makes the move identity `hmove`
(`deepestChain (framedParamsPivot (psiSplitRawGen q)) = movedC (deepestChain (framedParamsPivot q))
(Z0edit0 …)`) provable, feeding `deepestEFull_sq_sum_eq_of_chain_movedC` (`hsub3reg`) and, through
the diffeo triple of `DeepestPsiFlatCutGen`, the bridge `deepest_diffeo_bridge_gen_assembled`.

## Design (Codex-confirmed B′, `threads/genm-hstep2germs9/codex/`)

Per layer `s`, the reads packed back (via `regGaugeSlotEquiv.symm` for the gauge blocks `X'/Y'/Z'`
and `paramsEquivFlat (deepestM)` for the core block `T'`, mirroring the L=2 template
`psiSplitRawL2Core`) are the four blocks of an H-width matrix `psiReadBlk q s`, itself the
reduced-width relabel of a chain-width matrix `psiGhat q s`:

* **effective target** `D_s := movedC C Z0e (s) − fromBlocks 1 0 0 0` (subtract the `corM`-corner
  the additive framing supplies), `C := deepestChain (framedParamsPivot … q)`, `Z0e := Z0edit0 C L`;
* **interior** layers (`s ∉ {firstLayer, lastLayer}`, trivial frames): `psiGhat q s := D_s`;
* **first layer** (block-lower frame `Pf firstLayer`): `psiGhat q s := forcedDecodeLeft F0 D_s`;
* **last layer** (block-upper frame `Qf lastLayer`): `psiGhat q s := forcedDecodeRight Ql D_s`,

with `forcedDecodeLeft`/`Right` the FORCED reads verified in `DeepestFramedBoundaryMove` (so that
`frame·decode = target`). The frames are read off `Pf`/`Qf` in chain-width block form; the
last-layer `pivotThresholdSplit` collapses to `rThresholdSplit` at `J = frontEmbed` (in `hmove`).

## Status
DEFINITION only (this commit). `psiSplitRawGen` is a total `DeepestSplit → DeepestSplit`;
`Ring.inverse` supplies the frame-corner inverse (a unit near the deepest point). The move identity
`hmove` + the diffeo triple are the next items. No `sorry`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## The forced-decode block reads (matching `DeepestFramedBoundaryMove`) -/

/-- The layer-0 **forced left-frame decode**: given the effective target `D` and a block-lower frame
`F` (corner `P11 := F₁₁`, `P21 := F₂₁`, `Pinv := Ring.inverse P11`), the reads
`fromBlocks (Pinv·A) (Pinv·Y) (Z − P21·Pinv·A) (T − P21·Pinv·Y)` with `A,Y,Z,T = D`'s blocks. This
inverts a block-lower `fromBlocks P11 0 P21 1` frame (`fromBlocks_lowerFrame_mul_forcedDecode`). -/
noncomputable def forcedDecodeLeft {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (F : Matrix (r ⊕ a) (r ⊕ a) ℝ) (D : Matrix (r ⊕ a) (r ⊕ b) ℝ) : Matrix (r ⊕ a) (r ⊕ b) ℝ :=
  Matrix.fromBlocks
    (Ring.inverse F.toBlocks₁₁ * D.toBlocks₁₁)
    (Ring.inverse F.toBlocks₁₁ * D.toBlocks₁₂)
    (D.toBlocks₂₁ - F.toBlocks₂₁ * (Ring.inverse F.toBlocks₁₁ * D.toBlocks₁₁))
    (D.toBlocks₂₂ - F.toBlocks₂₁ * (Ring.inverse F.toBlocks₁₁ * D.toBlocks₁₂))

/-- The last-layer **forced right-frame decode**: given the effective target `D` and a block-upper
frame `Q` (corner `Q11 := Q₁₁`, `Q12 := Q₁₂`, `Qinv := Ring.inverse Q11`), the reads
`fromBlocks (A·Qinv) (Y − A·Qinv·Q12) (Z·Qinv) (T − Z·Qinv·Q12)`. This inverts a block-upper
`fromBlocks Q11 Q12 0 1` frame on the right (`fromBlocks_rightUpper_mul_forcedDecode`). -/
noncomputable def forcedDecodeRight {r a b : Type*} [Fintype r] [DecidableEq r]
    [Fintype b] [DecidableEq b]
    (Q : Matrix (r ⊕ b) (r ⊕ b) ℝ) (D : Matrix (r ⊕ a) (r ⊕ b) ℝ) : Matrix (r ⊕ a) (r ⊕ b) ℝ :=
  Matrix.fromBlocks
    (D.toBlocks₁₁ * Ring.inverse Q.toBlocks₁₁)
    (D.toBlocks₁₂ - D.toBlocks₁₁ * Ring.inverse Q.toBlocks₁₁ * Q.toBlocks₁₂)
    (D.toBlocks₂₁ * Ring.inverse Q.toBlocks₁₁)
    (D.toBlocks₂₂ - D.toBlocks₂₁ * Ring.inverse Q.toBlocks₁₁ * Q.toBlocks₁₂)

/-! ## The chain-width frames read off `Pf`/`Qf` -/

/-- The un-subtracted layer-0 width bridge:
`H (firstLayer hL).castSucc = deepestChainWidth H (firstLayer hL : ℕ)`. -/
theorem chainWidth_castSucc_firstLayer (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    H (firstLayer hL).castSucc = deepestChainWidth H (firstLayer hL : ℕ) :=
  deepestChainWidth_castSucc H (firstLayer hL : ℕ) (firstLayer hL).isLt

/-- The un-subtracted last-layer width bridge:
`H (lastLayer hL).succ = deepestChainWidth H ((lastLayer hL : ℕ) + 1)`. -/
theorem chainWidth_succ_lastLayer (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    H (lastLayer hL).succ = deepestChainWidth H ((lastLayer hL : ℕ) + 1) :=
  deepestChainWidth_succ H (lastLayer hL : ℕ) (lastLayer hL).isLt

/-- The layer-0 frame `Pf firstLayer` in chain-width block form
(`Fin r ⊕ Fin (chainWidth (firstLayer) − r)`). -/
noncomputable def psiFrame0 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ) :
    Matrix (Fin r ⊕ Fin (deepestChainWidth H (firstLayer hL : ℕ) - r))
      (Fin r ⊕ Fin (deepestChainWidth H (firstLayer hL : ℕ) - r)) ℝ :=
  Matrix.reindex (deepestChainSplit H r hr (firstLayer hL : ℕ))
      (deepestChainSplit H r hr (firstLayer hL : ℕ))
    (Matrix.reindex (finCongr (chainWidth_castSucc_firstLayer H hL))
      (finCongr (chainWidth_castSucc_firstLayer H hL))
      (Pf (firstLayer hL)))

/-- The last-layer frame `Qf lastLayer` in chain-width block form
(`Fin r ⊕ Fin (chainWidth (lastLayer+1) − r)`). -/
noncomputable def psiFrameLast (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    Matrix (Fin r ⊕ Fin (deepestChainWidth H ((lastLayer hL : ℕ) + 1) - r))
      (Fin r ⊕ Fin (deepestChainWidth H ((lastLayer hL : ℕ) + 1) - r)) ℝ :=
  Matrix.reindex (deepestChainSplit H r hr ((lastLayer hL : ℕ) + 1))
      (deepestChainSplit H r hr ((lastLayer hL : ℕ) + 1))
    (Matrix.reindex (finCongr (chainWidth_succ_lastLayer H hL))
      (finCongr (chainWidth_succ_lastLayer H hL))
      (Qf (lastLayer hL)))

/-! ## The per-layer chain-width read `psiGhat` and the H-width `readBlk` -/

/-- The effective target `D_s := movedC C Z0e (s) − corM` (chain-width;
`corM = fromBlocks 1 0 0 0`). -/
noncomputable def psiTargetD (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : ℕ) :
    Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ :=
  movedC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
      (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) s
    - Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0

/-- The chain-width decoded read `Ĝ_s`: interior `= D_s`, first layer `= forcedDecodeLeft F0 D_s`,
last layer `= forcedDecodeRight Ql D_s`. Dispatched by `s`'s position (`lastLayer` first, then
`firstLayer`, then interior). -/
noncomputable def psiGhat (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    Matrix (Fin r ⊕ Fin (deepestChainWidth H (s : ℕ) - r))
      (Fin r ⊕ Fin (deepestChainWidth H ((s : ℕ) + 1) - r)) ℝ :=
  if hlast : s = lastLayer hL then
    hlast ▸ forcedDecodeRight (psiFrameLast H r hr hL Qf)
      (psiTargetD H r hr hL J Pf Qf q (lastLayer hL : ℕ))
  else if hfirst : s = firstLayer hL then
    hfirst ▸ forcedDecodeLeft (psiFrame0 H r hr hL Pf)
      (psiTargetD H r hr hL J Pf Qf q (firstLayer hL : ℕ))
  else
    psiTargetD H r hr hL J Pf Qf q (s : ℕ)

/-- The H-width block form of the per-layer read (`psiGhat` relabeled from chain-width to
`H s.castSucc/succ` via `finCongr`). Its `toBlocks` are the gauge/core reads packed back below. -/
noncomputable def psiReadBlk (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    Matrix (Fin r ⊕ Fin (H s.castSucc - r)) (Fin r ⊕ Fin (H s.succ - r)) ℝ :=
  (psiGhat H r hr hL J Pf Qf q s).submatrix
    (Sum.map id (finCongr (chainWidth_castSucc_sub H r s)))
    (Sum.map id (finCongr (chainWidth_succ_sub H r s)))

/-- **The concrete general-`L` joint move** `psiSplitRawGen : DeepestSplit → DeepestSplit`. Packs
the per-layer reads (`psiReadBlk`'s four blocks): `X'/Y'/Z'` into the gauge slot via
`regGaugeSlotEquiv.symm`, `T'` into the core slot via `paramsEquivFlat (deepestM)`, mirroring L=2's
lens `psiSplitRawL2Core`. Its framed-chain image is `movedC (deepestChain (framedParamsPivot … q))
(Z0edit0 …)` — the move identity `hmove` the reg-germ consumes. -/
noncomputable def psiSplitRawGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  let g' : RegGaugeIdx H r → ℝ := fun idx =>
    match idx with
    | ⟨s, Sum.inl (Sum.inl (i, j))⟩ => (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₁₁ i j
    | ⟨s, Sum.inl (Sum.inr (i, j))⟩ => (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₁₂ i j
    | ⟨s, Sum.inr (i, j)⟩ => (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₂₁ i j
  let core' : Fin (flatDim (deepestM H r)) → ℝ :=
    paramsEquivFlat (deepestM H r) (fun s => (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₂₂)
  let regspec' := (regGaugeSlotEquiv H r hr hL).symm g'
  (regspec'.1, (core', regspec'.2))

end DLNFibre.DLN.RLCT
