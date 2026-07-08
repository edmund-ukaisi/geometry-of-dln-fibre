import DLNFibre.DLN.RLCT.Validate.DeepestPsiTripleGen
import DLNFibre.DLN.RLCT.Validate.DeepestChainUnitGerm

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiHraw0Gen` — `psiSplitRawGen 0 = 0` (#120 `hstep2`, Producer 1)

`hraw0` — the split origin is a fixed point of the general joint move `psiSplitRawGen`. At `q = 0` all
gauge/core reads vanish, so the framed chain layers are the pure corner `corM = fromBlocks 1 0 0 0`
(`framedParamsPivot_wstar_eq_corner` + `deepestChain_corner_eq_corM`); the moved chain is then fixed
(`movedC_eq_self_of_toBlocks₂₁_zero`), so `psiTargetD 0 s = 0`, hence the decoded reads `psiReadBlk 0 s`
all vanish (interior directly; boundary via `forcedDecode`-linearity), and packing zeros back gives `0`.
Fed to `DeepestPsiFlatCutGen`'s cutoff plumbing (`deepestPsiCutRaw_zero`, `deepestPsiFlatCut_fixpoint`, …).

This module first banks the frame-independent **foundations** (the two packing equivalences preserve `0`,
and the general-`L` chain layer of a corner parameter is `corM`).
-/

open Matrix

namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## Zero-preservation of the packing equivalences -/

/-- `paramsEquivFlat` maps the zero parameter tuple to the zero flat vector (it is ℝ-linear —
`paramsEquivFlatLinear`). -/
theorem paramsEquivFlat_zero (M : Fin (L + 1) → ℕ) :
    paramsEquivFlat M (0 : Params M) = 0 := by
  have h : paramsEquivFlat M (0 : Params M) = paramsEquivFlatLinear M 0 :=
    (congrFun (paramsEquivFlatLinear_coe M) 0).symm
  rw [h, map_zero]

/-- `paramsEquivFlat.symm` maps the zero flat vector to the zero parameter tuple. -/
theorem paramsEquivFlat_symm_zero (M : Fin (L + 1) → ℕ) :
    (paramsEquivFlat M).symm (0 : Fin (flatDim M) → ℝ) = 0 := by
  rw [← paramsEquivFlat_zero M, MeasurableEquiv.symm_apply_apply]

/-- `regGaugeSlotEquiv.symm` maps the zero read-function to the zero `(reg, gauge)` pair (from the
banked `regGaugeSlotEquiv_zero`). -/
theorem regGaugeSlotEquiv_symm_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (regGaugeSlotEquiv H r hr hL).symm 0 = 0 := by
  rw [← regGaugeSlotEquiv_zero H r hr hL, Homeomorph.symm_apply_apply]

/-! ## The general-`L` chain layer of a corner parameter is `corM`

`DeepestChainUnitGerm` supplies the `₁₁ = 1` / `₂₁ = 0` corner blocks; here we add the `₁₂`/`₂₂` blocks
and assemble the full `= corM`. -/

/-- Corner-parameter chain block `₁₂ = 0` (mirror of `deepestChainLayer_corner_toBlocks₁₁`; the row is a
`Fin r` index `< r`, the column is a complement index `≥ r`, so the corner `if i=j ∧ i<r` is `0`). -/
theorem deepestChainLayer_corner_toBlocks₁₂ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L)
    (hcor : A ⟨k, hk⟩ = Matrix.of (fun (i : Fin (H (⟨k, hk⟩ : Fin L).castSucc))
        (j : Fin (H (⟨k, hk⟩ : Fin L).succ)) => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) :
    (deepestChain H r hr A k).toBlocks₁₂
      = (0 : Matrix (Fin r) (Fin (deepestChainWidth H (k + 1) - r)) ℝ) := by
  funext i j
  rw [Matrix.toBlocks₁₂, Matrix.of_apply, deepestChain, Matrix.reindex_apply, Matrix.submatrix_apply,
    deepestChainSplit, deepestChainSplit, rThresholdSplit_symm_inl, rThresholdSplit_symm_inr,
    deepestChainLayer, dif_pos hk, Matrix.reindex_apply, Matrix.submatrix_apply, hcor, Matrix.of_apply,
    finCongr_symm, finCongr_symm, finCongr_apply, finCongr_apply, Matrix.zero_apply]
  simp only [Fin.coe_cast, Fin.coe_castLE]
  rw [if_neg]; rintro ⟨hval, hlt⟩; omega

/-- Corner-parameter chain block `₂₂ = 0` (both row and column are complement indices `≥ r`, so the
corner condition `i < r` fails). -/
theorem deepestChainLayer_corner_toBlocks₂₂ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L)
    (hcor : A ⟨k, hk⟩ = Matrix.of (fun (i : Fin (H (⟨k, hk⟩ : Fin L).castSucc))
        (j : Fin (H (⟨k, hk⟩ : Fin L).succ)) => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) :
    (deepestChain H r hr A k).toBlocks₂₂
      = (0 : Matrix (Fin (deepestChainWidth H k - r)) (Fin (deepestChainWidth H (k + 1) - r)) ℝ) := by
  funext i j
  rw [Matrix.toBlocks₂₂, Matrix.of_apply, deepestChain, Matrix.reindex_apply, Matrix.submatrix_apply,
    deepestChainSplit, deepestChainSplit, rThresholdSplit_symm_inr, rThresholdSplit_symm_inr,
    deepestChainLayer, dif_pos hk, Matrix.reindex_apply, Matrix.submatrix_apply, hcor, Matrix.of_apply,
    finCongr_symm, finCongr_symm, finCongr_apply, finCongr_apply, Matrix.zero_apply]
  simp only [Fin.coe_cast, Fin.coe_castLE]
  rw [if_neg]; rintro ⟨hval, hlt⟩; omega

/-- **The general-`L` chain layer of a corner parameter is `corM`.** For `k < L`, if the `k`-th parameter
is the split corner shape, the abstract chain layer is `fromBlocks 1 0 0 0`. Assembles the four
corner-block reads via `fromBlocks_toBlocks`. -/
theorem deepestChain_corner_eq_corM (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L)
    (hcor : A ⟨k, hk⟩ = Matrix.of (fun (i : Fin (H (⟨k, hk⟩ : Fin L).castSucc))
        (j : Fin (H (⟨k, hk⟩ : Fin L).succ)) => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) :
    deepestChain H r hr A k
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
  rw [← Matrix.fromBlocks_toBlocks (deepestChain H r hr A k),
    deepestChainLayer_corner_toBlocks₁₁ H r hr A k hk hcor,
    deepestChainLayer_corner_toBlocks₁₂ H r hr A k hk hcor,
    deepestChainLayer_corner_toBlocks₂₁ H r hr A k hk hcor,
    deepestChainLayer_corner_toBlocks₂₂ H r hr A k hk hcor]

end DLNFibre.DLN.RLCT
