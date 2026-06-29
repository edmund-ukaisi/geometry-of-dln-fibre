import DLNFibre.DLN.RLCT.Validate.DeepestSplitConcrete

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFrameRaw` — the matrix-block layer-entry identity (PIN2 step (1))

The genuinely-new content joining the BANKED round-trip **index half** (`gaugeReadX/Y/Z_deepestSplit` in
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

Together these give the per-arm `gaugeReadX/Y/Z (deepestSplit w) s i j = (deviation block of (paramsEquivFlat.symm
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

/-! ## PIN2 step (1)+(2) — the four-arm raw decode + the entry-wise `fromBlocks = deviation`

The genuinely-new geometric glue joining the BANKED index round-trip (`gaugeReadX/Y/Z_deepestSplit`,
`DeepestSplitConcrete`) + the index identity (`deepestRoleIndexEquiv_symm_recombine`) + the flat
decode (`paramsEquivFlat_apply_equivFin`) to the RAW layer entry of the flat deviation
`(paramsEquivFlat.symm (w − wstar))`. The four arms (`gaugeReadX/Y/Z/T_deepestSplit_raw`) decode each
gauge / core block to the corresponding entry of the raw layer matrix at the `r`-threshold block
position; `reindex_fromBlocks_reads_eq_deviation` assembles them into the per-layer matrix identity
`reindex(fromBlocks gaugeReadX gaugeReadY gaugeReadZ Tcore) = (paramsEquivFlat.symm (w − wstar)) s`. All
J-independent (no boundary-frame / pivot-set data). -/

/-- Forward of `rThresholdSplit` on a "top-block" index `i.castLE ha` is `Sum.inl i`. -/
theorem rThresholdSplit_castLE (r a : ℕ) (ha : r ≤ a) (k : Fin r) :
    (rThresholdSplit r a ha) (k.castLE ha) = Sum.inl k := by
  rw [← rThresholdSplit_symm_inl r a ha k, Equiv.apply_symm_apply]

/-- Forward of `rThresholdSplit` on a "bottom-block" index `⟨r + k, _⟩` is `Sum.inr k`. -/
theorem rThresholdSplit_natAdd (r a : ℕ) (ha : r ≤ a) (k : Fin (a - r)) :
    (rThresholdSplit r a ha) ⟨r + k, by omega⟩ = Sum.inr k := by
  rw [← rThresholdSplit_symm_inr r a ha k, Equiv.apply_symm_apply]

/-- `gaugeReadX (deepestSplit w) s i j` decoded to the raw deviation entry of `(paramsEquivFlat.symm
(w − wstar)) s` at the top-left `r × r` block (row `i.castLE`, column `j.castLE`). -/
theorem gaugeReadX_deepestSplit_raw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (s : Fin L) (i j : Fin r) :
    gaugeReadX H r hr hL ((deepestSplit H r hr hL wstar w).1,
        (deepestSplit H r hr hL wstar w).2.2) s i j
      = (paramsEquivFlat H).symm (w - wstar) s (i.castLE (hr s.castSucc)) (j.castLE (hr s.succ)) := by
  rw [gaugeReadX_deepestSplit, deepestRoleIndexEquiv_symm_recombine]
  conv_lhs => rw [← (paramsEquivFlat H).apply_symm_apply (w - wstar)]
  rw [paramsEquivFlat_apply_equivFin]
  have hidx : (roleSplitIdx H r hr).symm (Sum.inl ⟨s, Sum.inl (Sum.inl (i, j))⟩)
      = (⟨⟨s, i.castLE (hr s.castSucc)⟩, j.castLE (hr s.succ)⟩ : FlatIdx H) := by
    rw [Equiv.symm_apply_eq]
    unfold roleSplitIdx flatIdxLayerProd layerEntrySplit
    simp only [Equiv.trans_apply, Equiv.sigmaAssoc, Equiv.coe_fn_mk, Equiv.sigmaCongrRight_apply,
      Equiv.sigmaEquivProd_apply, Equiv.sigmaSumDistrib_apply, Equiv.sumCongr_apply,
      Equiv.prodCongr_apply, Prod.map, Sum.map_inl, Equiv.refl_apply, rThresholdSplit_castLE,
      Equiv.sumProdDistrib_apply_left, Equiv.prodSumDistrib_apply_left,
      Equiv.sumAssoc_symm_apply_inl]
  rw [hidx]

/-- `gaugeReadY (deepestSplit w) s i j` decoded to the raw deviation entry at the top-right `r × (H_{s+1}−r)`
block (row `i.castLE`, column `⟨r + j, _⟩`). -/
theorem gaugeReadY_deepestSplit_raw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (s : Fin L) (i : Fin r) (j : Fin (H s.succ - r)) :
    gaugeReadY H r hr hL ((deepestSplit H r hr hL wstar w).1,
        (deepestSplit H r hr hL wstar w).2.2) s i j
      = (paramsEquivFlat H).symm (w - wstar) s (i.castLE (hr s.castSucc))
          ⟨r + j, by have := hr s.succ; have := j.isLt; omega⟩ := by
  rw [gaugeReadY_deepestSplit, deepestRoleIndexEquiv_symm_recombine]
  conv_lhs => rw [← (paramsEquivFlat H).apply_symm_apply (w - wstar)]
  rw [paramsEquivFlat_apply_equivFin]
  have hb : r + (j : ℕ) < H s.succ := by have := hr s.succ; have := j.isLt; omega
  have hidx : (roleSplitIdx H r hr).symm (Sum.inl ⟨s, Sum.inl (Sum.inr (i, j))⟩)
      = (⟨⟨s, i.castLE (hr s.castSucc)⟩, ⟨r + j, hb⟩⟩ : FlatIdx H) := by
    rw [Equiv.symm_apply_eq]
    unfold roleSplitIdx flatIdxLayerProd layerEntrySplit
    simp only [Equiv.trans_apply, Equiv.sigmaAssoc, Equiv.coe_fn_mk, Equiv.sigmaCongrRight_apply,
      Equiv.sigmaEquivProd_apply, Equiv.sigmaSumDistrib_apply, Equiv.sumCongr_apply,
      Equiv.prodCongr_apply, Prod.map, Sum.map_inl, Equiv.refl_apply,
      rThresholdSplit_castLE, rThresholdSplit_natAdd, Equiv.sumProdDistrib_apply_left,
      Equiv.prodSumDistrib_apply_right, Equiv.sumAssoc_symm_apply_inl]
  rw [hidx]

/-- `gaugeReadZ (deepestSplit w) s i j` decoded to the raw deviation entry at the bottom-left
`(H_s−r) × r` block (row `⟨r + i, _⟩`, column `j.castLE`). -/
theorem gaugeReadZ_deepestSplit_raw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (s : Fin L) (i : Fin (H s.castSucc - r)) (j : Fin r) :
    gaugeReadZ H r hr hL ((deepestSplit H r hr hL wstar w).1,
        (deepestSplit H r hr hL wstar w).2.2) s i j
      = (paramsEquivFlat H).symm (w - wstar) s ⟨r + i, by have := hr s.castSucc; have := i.isLt; omega⟩
          (j.castLE (hr s.succ)) := by
  rw [gaugeReadZ_deepestSplit, deepestRoleIndexEquiv_symm_recombine]
  conv_lhs => rw [← (paramsEquivFlat H).apply_symm_apply (w - wstar)]
  rw [paramsEquivFlat_apply_equivFin]
  have hb : r + (i : ℕ) < H s.castSucc := by have := hr s.castSucc; have := i.isLt; omega
  have hidx : (roleSplitIdx H r hr).symm (Sum.inl ⟨s, Sum.inr (i, j)⟩)
      = (⟨⟨s, ⟨r + i, hb⟩⟩, j.castLE (hr s.succ)⟩ : FlatIdx H) := by
    rw [Equiv.symm_apply_eq]
    unfold roleSplitIdx flatIdxLayerProd layerEntrySplit
    simp only [Equiv.trans_apply, Equiv.sigmaAssoc, Equiv.coe_fn_mk, Equiv.sigmaCongrRight_apply,
      Equiv.sigmaEquivProd_apply, Equiv.sigmaSumDistrib_apply, Equiv.sumCongr_apply,
      Equiv.prodCongr_apply, Prod.map, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
      rThresholdSplit_castLE, rThresholdSplit_natAdd, Equiv.sumProdDistrib_apply_right,
      Equiv.prodSumDistrib_apply_left, Equiv.sumAssoc_symm_apply_inr_inl]
  rw [hidx]

/-- Core recombine: `deepestRoleIndexEquiv.symm (Sum.inr (Sum.inl m))` routes back to the core flat
index (the middle `flatM` summand → the reduced-chain flat coordinate). -/
theorem deepestRoleIndexEquiv_symm_core (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (m : Fin (flatDim (deepestM H r))) :
    (deepestRoleIndexEquiv H r hr hL).symm (Sum.inr (Sum.inl m))
      = (Fintype.equivFin (FlatIdx H)) ((roleSplitIdx H r hr).symm
          (Sum.inr ((Fintype.equivFin (FlatIdx (deepestM H r))).symm m))) := by
  classical
  rw [Equiv.symm_apply_eq, deepestRoleIndexEquiv]
  conv_rhs => erw [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.trans_apply]
  simp only [Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumAssoc_apply_inr, Equiv.sumComm_apply, Sum.swap_inr]
  congr 2
  exact (Equiv.apply_symm_apply _ m).symm

/-- The core-arm `roleSplitIdx.symm` decode: `Sum.inr ⟨⟨s,a⟩,b⟩` lands on the bottom-right block of
`FlatIdx H` — row `⟨r + a, _⟩`, column `⟨r + b, _⟩`. -/
theorem roleSplitIdx_symm_core (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (s : Fin L) (a : Fin (H s.castSucc - r)) (b : Fin (H s.succ - r)) :
    (roleSplitIdx H r hr).symm (Sum.inr ⟨⟨s, a⟩, b⟩)
      = (⟨(⟨s, ⟨r + a, by have := a.isLt; have := hr s.castSucc; omega⟩⟩ : FlatRowIdx H),
          (⟨r + b, by have := b.isLt; have := hr s.succ; omega⟩ : Fin (H s.succ))⟩ : FlatIdx H) := by
  rw [Equiv.symm_apply_eq]
  unfold roleSplitIdx flatIdxLayerProd layerEntrySplit
  simp only [Equiv.trans_apply, Equiv.sigmaAssoc, Equiv.sigmaEquivProd, Equiv.coe_fn_mk,
    Equiv.sigmaCongrRight_apply, Equiv.sigmaSumDistrib_apply, Equiv.sumCongr_apply,
    Equiv.prodCongr_apply, Prod.map, Sum.map_inr, rThresholdSplit_natAdd,
    Equiv.sumProdDistrib_apply_right, Equiv.prodSumDistrib_apply_right,
    Equiv.sumAssoc_symm_apply_inr_inr]
  rfl

/-- **The T-core raw decode.** The core slot of `deepestSplit w`, pulled back through
`paramsEquivFlat (deepestM H r)` and read at layer `s`, row `a`, column `b` (reduced widths), equals
the raw deviation `(paramsEquivFlat H).symm (w − wstar)` at the bottom-right block of layer `s`
(row `⟨r + a, _⟩`, column `⟨r + b, _⟩`). The T-core analogue of `gaugeReadX/Y/Z_deepestSplit_raw`. -/
theorem readT_deepestSplit_raw (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ)
    (s : Fin L) (a : Fin (H s.castSucc - r)) (b : Fin (H s.succ - r)) :
    (paramsEquivFlat (deepestM H r)).symm (deepestSplit H r hr hL wstar w).2.1 s a b
      = (paramsEquivFlat H).symm (w - wstar) s
          ⟨r + a, by have := a.isLt; have := hr s.castSucc; omega⟩
          ⟨r + b, by have := b.isLt; have := hr s.succ; omega⟩ := by
  classical
  set idx' : FlatIdx (deepestM H r) := ⟨⟨s, a⟩, b⟩ with hidx'
  have hA : (paramsEquivFlat (deepestM H r)).symm (deepestSplit H r hr hL wstar w).2.1 s a b
      = (deepestSplit H r hr hL wstar w).2.1
          (Fintype.equivFin (FlatIdx (deepestM H r)) idx') := by
    rw [← paramsEquivFlat_apply_equivFin (deepestM H r)
        ((paramsEquivFlat (deepestM H r)).symm (deepestSplit H r hr hL wstar w).2.1) idx',
      (paramsEquivFlat (deepestM H r)).apply_symm_apply]
  rw [hA, deepestSplit_core_apply]
  change (Equiv.piCongrLeft (fun _ => ℝ) (deepestRoleIndexEquiv H r hr hL)) (w - wstar)
      (Sum.inr (Sum.inl (Fintype.equivFin (FlatIdx (deepestM H r)) idx'))) = _
  rw [Equiv.piCongrLeft_apply_eq_cast]
  simp only [cast_eq]
  rw [deepestRoleIndexEquiv_symm_core, Equiv.symm_apply_apply]
  conv_lhs => rw [← (paramsEquivFlat H).apply_symm_apply (w - wstar)]
  rw [paramsEquivFlat_apply_equivFin, roleSplitIdx_symm_core]

set_option linter.style.longLine false in
/-- **The consolidating block-read identity** (the entry-wise `fromBlocks = raw deviation`). Reindexing
the per-layer `fromBlocks` of the four reads (X/Y/Z reg-gauge blocks + the T-core block, via the
`r`-threshold row/column split) recovers the raw layer matrix `((paramsEquivFlat H).symm (w − wstar)) s`.
The four `fromBlocks` arms decode via `gaugeReadX/Y/Z/T_deepestSplit_raw` at the recovered split index. -/
theorem reindex_fromBlocks_reads_eq_deviation (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ) (s : Fin L) :
    Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
        (rThresholdSplit r (H s.succ) (hr s.succ)).symm
        (Matrix.fromBlocks
          (gaugeReadX H r hr hL ((deepestSplit H r hr hL wstar w).1, (deepestSplit H r hr hL wstar w).2.2) s)
          (gaugeReadY H r hr hL ((deepestSplit H r hr hL wstar w).1, (deepestSplit H r hr hL wstar w).2.2) s)
          (gaugeReadZ H r hr hL ((deepestSplit H r hr hL wstar w).1, (deepestSplit H r hr hL wstar w).2.2) s)
          ((paramsEquivFlat (deepestM H r)).symm (deepestSplit H r hr hL wstar w).2.1 s))
      = ((paramsEquivFlat H).symm (w - wstar)) s := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_symm]
  rcases hi : (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) i with a | a <;>
    rcases hj : (rThresholdSplit r (H s.succ) (hr s.succ)) j with b | b
  · rw [Matrix.fromBlocks_apply₁₁, gaugeReadX_deepestSplit_raw]
    rw [show i = (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inl a) by
          rw [← hi, Equiv.symm_apply_apply],
        show j = (rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inl b) by
          rw [← hj, Equiv.symm_apply_apply],
      rThresholdSplit_symm_inl, rThresholdSplit_symm_inl]
  · rw [Matrix.fromBlocks_apply₁₂, gaugeReadY_deepestSplit_raw]
    rw [show i = (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inl a) by
          rw [← hi, Equiv.symm_apply_apply],
        show j = (rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr b) by
          rw [← hj, Equiv.symm_apply_apply],
      rThresholdSplit_symm_inl, rThresholdSplit_symm_inr]
  · rw [Matrix.fromBlocks_apply₂₁, gaugeReadZ_deepestSplit_raw]
    rw [show i = (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr a) by
          rw [← hi, Equiv.symm_apply_apply],
        show j = (rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inl b) by
          rw [← hj, Equiv.symm_apply_apply],
      rThresholdSplit_symm_inr, rThresholdSplit_symm_inl]
  · rw [Matrix.fromBlocks_apply₂₂, readT_deepestSplit_raw]
    rw [show i = (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr a) by
          rw [← hi, Equiv.symm_apply_apply],
        show j = (rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr b) by
          rw [← hj, Equiv.symm_apply_apply],
      rThresholdSplit_symm_inr, rThresholdSplit_symm_inr]

end DLNFibre.DLN.RLCT
