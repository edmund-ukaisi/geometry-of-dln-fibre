import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGen

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGenMove` — reads round-trip (#120 item 2)

The bridge from the packing of `psiSplitRawGen` (`DeepestPsiSplitRawGen`) back to the per-layer read
blocks `psiReadBlk`, and the INTERIOR half of the move identity `hmove`.

`psiSplitRawGen q` packs the target reads through `regGaugeSlotEquiv.symm` (gauge blocks) and
`paramsEquivFlat (deepestM)` (core block). Reading them back — `gaugeReadX/Y/Z` and the core read of
`psiSplitRawGen q` — recovers exactly `psiReadBlk q s`'s four `toBlocks`, since both equivs
round-trip (`apply_symm_apply` / `symm_apply_apply`) and the packed `g'` reduces on each
`RegGaugeIdx` tag. These four facts are the bridge for `hmove`; composed with the banked
`deepestChain_framedParamsPivot_blocks_of_frame_one`, they give the interior-layer move identity.

## Status
Round-trip lemmas (the packing → `psiReadBlk` bridge). Pure equiv round-trip + `Matrix` block
algebra over `ℝ`. The interior/boundary per-layer moves + the `funext s` assembly of `hmove` are the
remaining work. No `sorry`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## The reads round-trip: `psiSplitRawGen`'s gauge/core reads = `psiReadBlk`'s blocks -/

/-- The gauge slot of `psiSplitRawGen q` is `regGaugeSlotEquiv.symm` of the packed `g'`; so applying
`regGaugeSlotEquiv` recovers `g'`. The single fact all four read round-trips share. -/
theorem regGaugeSlotEquiv_psiSplitRawGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    regGaugeSlotEquiv H r hr hL ((psiSplitRawGen H r hr hL J Pf Qf q).1,
        (psiSplitRawGen H r hr hL J Pf Qf q).2.2)
      = fun idx =>
          match idx with
          | ⟨s, Sum.inl (Sum.inl (i, j))⟩ => (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₁₁ i j
          | ⟨s, Sum.inl (Sum.inr (i, j))⟩ => (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₁₂ i j
          | ⟨s, Sum.inr (i, j)⟩ => (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₂₁ i j := by
  change regGaugeSlotEquiv H r hr hL
      (((regGaugeSlotEquiv H r hr hL).symm _).1, ((regGaugeSlotEquiv H r hr hL).symm _).2) = _
  rw [Prod.mk.eta, Homeomorph.apply_symm_apply]
  rfl

/-- Read-back of the `X` block: `gaugeReadX (psiSplitRawGen q) s = (psiReadBlk q s).toBlocks₁₁`. -/
theorem gaugeReadX_psiSplitRawGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    gaugeReadX H r hr hL ((psiSplitRawGen H r hr hL J Pf Qf q).1,
        (psiSplitRawGen H r hr hL J Pf Qf q).2.2) s
      = (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₁₁ := by
  funext i j
  rw [gaugeReadX, Matrix.of_apply, regGaugeSlotEquiv_psiSplitRawGen]

/-- Read-back of the `Y` block: `gaugeReadY (psiSplitRawGen q) s = (psiReadBlk q s).toBlocks₁₂`. -/
theorem gaugeReadY_psiSplitRawGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    gaugeReadY H r hr hL ((psiSplitRawGen H r hr hL J Pf Qf q).1,
        (psiSplitRawGen H r hr hL J Pf Qf q).2.2) s
      = (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₁₂ := by
  funext i j
  rw [gaugeReadY, Matrix.of_apply, regGaugeSlotEquiv_psiSplitRawGen]

/-- Read-back of the `Z` block: `gaugeReadZ (psiSplitRawGen q) s = (psiReadBlk q s).toBlocks₂₁`. -/
theorem gaugeReadZ_psiSplitRawGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    gaugeReadZ H r hr hL ((psiSplitRawGen H r hr hL J Pf Qf q).1,
        (psiSplitRawGen H r hr hL J Pf Qf q).2.2) s
      = (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₂₁ := by
  funext i j
  rw [gaugeReadZ, Matrix.of_apply, regGaugeSlotEquiv_psiSplitRawGen]

/-- Read-back of the core block:
`(paramsEquivFlat (deepestM)).symm (psiSplitRawGen q).2.1 s = (psiReadBlk q s).toBlocks₂₂`. -/
theorem coreRead_psiSplitRawGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawGen H r hr hL J Pf Qf q).2.1 s
      = (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₂₂ := by
  change (paramsEquivFlat (deepestM H r)).symm
      ((paramsEquivFlat (deepestM H r))
        (fun s => (psiReadBlk H r hr hL J Pf Qf q s).toBlocks₂₂)) s = _
  rw [(paramsEquivFlat (deepestM H r)).symm_apply_apply]

end DLNFibre.DLN.RLCT
