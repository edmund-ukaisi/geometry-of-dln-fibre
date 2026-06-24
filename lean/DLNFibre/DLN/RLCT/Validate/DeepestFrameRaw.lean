import DLNFibre.DLN.RLCT.Validate.DeepestSplitConcrete

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFrameRaw` — the matrix-block layer-entry identity (PIN2 step (1))

The genuinely-new content joining the BANKED round-trip **index half** (`readX/Y/Z_deepestSplit` in
`DeepestSplitConcrete`) to the **raw layer entry** of the flat deviation `(paramsEquivFlat.symm w −
deepestPoint)`. Two J-INDEPENDENT atoms (independent of the boundary-frame column-split / pivot set):

* `deepestRoleIndexEquiv_symm_recombine` — the index identity
  `deepestRoleIndexEquiv.symm (regGaugeRecombine (regGaugeIdxSplit a)) =
   Fintype.equivFin (FlatIdx H) (roleSplitIdx.symm (Sum.inl a))` for ALL `a : RegGaugeIdx H r`.
  The two `regGaugeIdxSplit` enumerations cancel; the core `Fintype.equivFin (FlatIdx M)` never
  appears on a `regGaugeRecombine` output (its image is the reg/gauge summand only).
* `paramsEquivFlat_apply_equivFin` — the flat decode
  `paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2`
  (the `arrowCongr'`/`piCurry`/`Sigma.uncurry` unfold).

Together these give the per-arm `readX/Y/Z (deepestSplit w) s i j = (deviation block of (paramsEquivFlat.symm
w − deepestPoint) at the decoded flat index)`. (Note: the `Equiv`/`MeasurableEquiv` `trans`/`symm`
applications need `erw` — the keyed `rw`/`simp` matcher misses the `EquivLike`-coercion form at v4.29.)
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The index identity** (PIN2 step (1), generic over `a : RegGaugeIdx H r`). Reversing the
`deepestRoleIndexEquiv` chain on a `regGaugeRecombine` output cancels the two `regGaugeIdxSplit`
enumerations and lands on `Fintype.equivFin (FlatIdx H) (roleSplitIdx.symm (Sum.inl a))`. The core
enumeration `Fintype.equivFin (FlatIdx (deepestM))` does NOT appear: `regGaugeRecombine`'s image is
disjoint from the middle (`flatM`) summand, so the `sumComm`/`sumAssoc` reversal routes every recombine
output back through the reg-gauge half. -/
theorem deepestRoleIndexEquiv_symm_recombine (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (a : RegGaugeIdx H r) :
    (deepestRoleIndexEquiv H r hr hL).symm
        (regGaugeRecombine (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
          (regGaugeIdxSplit H r hr hL a))
      = (Fintype.equivFin (FlatIdx H)) ((roleSplitIdx H r hr).symm (Sum.inl a)) := by
  classical
  rw [Equiv.symm_apply_eq, deepestRoleIndexEquiv]
  conv_rhs => erw [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.trans_apply]
  rcases h : regGaugeIdxSplit H r hr hL a with k | g
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, h, Equiv.sumAssoc_apply_inl_inl,
      Equiv.refl_apply, regGaugeRecombine, Sum.elim_inl]
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, h, Sum.map_inr, Equiv.sumAssoc_apply_inl_inr,
      Equiv.sumComm_apply, Sum.swap_inl, regGaugeRecombine, Sum.elim_inr]

/-- **The flat decode** `paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2`
— a flat coordinate at the `Fintype.equivFin` image of a `FlatIdx` entry reads back the layer matrix
entry `A s i j` (where `idx = ⟨⟨s, i⟩, j⟩`). The `arrowCongr'`/`piCurry`/`Sigma.uncurry` unfold. -/
theorem paramsEquivFlat_apply_equivFin (H : Fin (L + 1) → ℕ) (A : Params H) (idx : FlatIdx H) :
    paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2 := by
  unfold paramsEquivFlat
  erw [MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply]
  simp only [MeasurableEquiv.coe_piCurry_symm]
  erw [Equiv.arrowCongr_apply]
  simp only [Function.comp_apply]
  erw [Equiv.symm_apply_apply]
  rfl

/-- `rThresholdSplit.symm (Sum.inl i)` is the `castLE` of `i` into the first `r` indices — the inverse
of the per-vertex `r`-threshold row split on the regular (top) block. J-independent. -/
theorem rThresholdSplit_symm_inl (r a : ℕ) (ha : r ≤ a) (i : Fin r) :
    (rThresholdSplit r a ha).symm (Sum.inl i) = i.castLE ha := by
  unfold rThresholdSplit
  simp only [Equiv.symm_trans_apply, finCongr_symm, Equiv.symm_symm,
    finSumFinEquiv_apply_left, finCongr_apply]
  apply Fin.ext; simp [Fin.castLE, Fin.castAdd]

/-- `rThresholdSplit.symm (Sum.inr i)` is `r + i` — the inverse of the threshold split on the reduced
(bottom) `a − r` block. J-independent. -/
theorem rThresholdSplit_symm_inr (r a : ℕ) (ha : r ≤ a) (i : Fin (a - r)) :
    (rThresholdSplit r a ha).symm (Sum.inr i) = ⟨r + i, by omega⟩ := by
  unfold rThresholdSplit
  simp only [Equiv.symm_trans_apply, finCongr_symm, Equiv.symm_symm,
    finSumFinEquiv_apply_right, finCongr_apply]
  apply Fin.ext; simp [Fin.natAdd]

end DLNFibre.DLN.RLCT
