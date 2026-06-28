import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2Conj` — the CONJUGATED L=2 joint-Ψ apparatus

The conjugated parallel of the bare joint-Ψ apparatus in `DeepestDiffeoBridgeL2` (Step Ψ_conj of the
atom-free L2 bridge `hstep2 = Step Θ ∘ Step Ψ_conj`). Every block is the bare's with the pivot base
`1` replaced by the deepest block `M̄_s := deepBlk·_s` (`DeepestSchurShift`):

* pivots `A0c = deepBlkA_0 + readX_0`, `A1c = deepBlkA_last + readX_last`;
* off-diagonals `Y0c = M̄Y_0 + readY_0` (cols cast), `Z1c = M̄Z_last + readZ_last`,
  `Y1c = M̄Y_last + readY_last`;
* `T1c = coreLast` (the core block is shared — the conjugation lives in the pivots/off-diagonals).

**KEY (de-risking): `D(Ψ_conj)(0) = id`, EXACTLY like the bare.** At the split origin all reads vanish
AND at the two L=2 boundary layers the deepest off-diagonal blocks vanish: `M̄Y_0 = 0`
(`deepBlkY_layer0_zero`, layer-0 cols ≥ r vanish) and `M̄Z_last = 0` (`deepBlkZ_layerLast_zero`,
layer-(L−1) rows ≥ r vanish). So at `q = 0`, `Y0c = Z1c = 0`, hence `K = R = W − 1 = 0`,
`S1 = T1 = 0`, `T1'c − T1c = 0`, `Y1'c − Y1c = 0` — the SAME vanishing pattern as the bare. The pivots
`A0c, A1c` are deepest-block UNITS (not `1`) at `0` but every correction carries a `Z1c`/`Y0c` factor,
so their non-`1`-ness is invisible to the derivative. The conjugated S4 reuses `e = refl`.

`hbdy : ∀ s, deepBlkY_s = 0 ∨ deepBlkZ_s = 0` is the L=2 boundary structure (both layers boundary).
`hDA : ∀ s, IsUnit (deepBlkA_s)` is the pivot-base unit-ness (the foundation seam — discharged at the
wire, layer-0 via `deepestPoint_leadingBlock_isUnit`/htop).
-/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Boundary vanishing of the deepest off-diagonal blocks (`L = 2`)

`M̄Y_0 = 0` (layer-0 columns ≥ r vanish; `toBlocks₁₂` reads only such columns) and `M̄Z_last = 0`
(layer-(L−1) rows ≥ r vanish; `toBlocks₂₁` reads only such rows). These make `Y0c = Z1c = 0` at the
split origin — the conjugated S4 derivative-vanishing mechanism. -/

/-- `M̄Y_s = deepBlkY_s = 0` at **layer 0** (`L ≥ 2`): `toBlocks₁₂` reads cols `≥ r`, which vanish. -/
theorem deepBlkY_layer0_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (s : Fin L)
    (hs : (s : ℕ) = 0) :
    deepBlkY H r B hB hr hL s = 0 := by
  funext i j
  change (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inl i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr j)) = 0
  rw [rThresholdSplit_symm_inr]
  exact deepestPoint_layer0_cols_vanish H r B hB hr hL s hL2 hs _ _ (by simp)

/-- `M̄Z_s = deepBlkZ_s = 0` at **layer (L−1)** (`L ≥ 2`): `toBlocks₂₁` reads rows `≥ r`, vanish. -/
theorem deepBlkZ_layerLast_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (s : Fin L)
    (hs : (s : ℕ) + 1 = L) :
    deepBlkZ H r B hB hr hL s = 0 := by
  funext i j
  change (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inl j)) = 0
  rw [rThresholdSplit_symm_inr]
  exact deepestPoint_layerLast_rows_vanish H r B hB hr hL s hL2 hs _ _ (by simp)

/-- The **L=2 boundary hypothesis** holds unconditionally (both layers are boundary at `L = 2`):
layer 0 has `M̄Y_0 = 0`, layer 1 = layer-(L−1) has `M̄Z_1 = 0`. -/
theorem deepBlk_boundary_of_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0 := by
  intro s
  rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
  · exact Or.inl (deepBlkY_layer0_zero H r B hB hr hL (by omega) s hs0)
  · refine Or.inr (deepBlkZ_layerLast_zero H r B hB hr hL (by omega) s ?_)
    have : (s : ℕ) < L := s.isLt
    omega

/-! ## S0 — the conjugated named blocks (`…Conj`), mirroring `l2A0..l2Y1p` with pivots swapped

The conjugated per-layer blocks are the bare's with pivot base `1` → `deepBlkA_s` and the off-diagonals
the conjugated reindexed-decode reads `deepBlk·_s + read·_s` — i.e. the actual blocks of
`reindex(decode q)_s` that the conjugated readback (`absorbedCoreConj_eq_schurCore`) reads. The core
block `T1c = coreLast` is the SAME as the bare (the conjugation lives in the pivots/off-diagonals). -/

/-- `A0c = deepBlkA_0 + readX_0` (conjugated layer-0 pivot; bare was `1 + readX_0`). -/
noncomputable def l2A0Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : Matrix (Fin r) (Fin r) ℝ :=
  let s0 : Fin L := ⟨0, by omega⟩
  deepBlkA H r B hB hr hL s0 + readX H r hr hL (q.1, q.2.2) s0

/-- `A1c = deepBlkA_last + readX_last` (conjugated last-layer pivot). -/
noncomputable def l2A1Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : Matrix (Fin r) (Fin r) ℝ :=
  deepBlkA H r B hB hr hL (lastLayer hL) + readX H r hr hL (q.1, q.2.2) (lastLayer hL)

/-- `Y0c = deepBlkY_0 + readY_0`, cols bridged to the middle interface (`midWidth_eq_of_L2`). -/
noncomputable def l2Y0Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  let s0 : Fin L := ⟨0, by omega⟩
  Matrix.reindex (Equiv.refl (Fin r)) (finCongr (midWidth_eq_of_L2 H r hL hL2eq))
    (deepBlkY H r B hB hr hL s0 + readY H r hr hL (q.1, q.2.2) s0)

/-- `Z1c = deepBlkZ_last + readZ_last` (conjugated last-layer Z). -/
noncomputable def l2Z1Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin r) ℝ :=
  deepBlkZ H r B hB hr hL (lastLayer hL) + readZ H r hr hL (q.1, q.2.2) (lastLayer hL)

/-- `Y1c = deepBlkY_last + readY_last` (conjugated last-layer Y; the reg block the move edits). -/
noncomputable def l2Y1Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  deepBlkY H r B hB hr hL (lastLayer hL) + readY H r hr hL (q.1, q.2.2) (lastLayer hL)

/-- `T1c = coreLast` (the core block the move edits — SAME as the bare `l2T1`). -/
noncomputable def l2T1Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).succ)) ℝ := coreLast H r hL q

/-- The conjugated full-product `(1,1)` block `P00c = A0c·A1c + Y0c·Z1c`. -/
noncomputable def l2P00Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : Matrix (Fin r) (Fin r) ℝ :=
  l2A0Conj H r B hB hr hL q * l2A1Conj H r B hB hr hL q
    + l2Y0Conj H r B hB hr hL hL2eq q * l2Z1Conj H r B hB hr hL q

/-- The conjugated `Kc = Z1c·P00c⁻¹·Y0c`. -/
noncomputable def l2KConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  l2Z1Conj H r B hB hr hL q * (l2P00Conj H r B hB hr hL hL2eq q)⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q

/-- The conjugated `Rc = Z1c·A1c⁻¹·A0c⁻¹·Y0c` (so `Wc = 1 + Rc`). -/
noncomputable def l2RConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹
    * l2Y0Conj H r B hB hr hL hL2eq q

/-- The conjugated `Wc = 1 + Z1c·A1c⁻¹·A0c⁻¹·Y0c`. -/
noncomputable def l2WConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  1 + l2RConj H r B hB hr hL hL2eq q

/-- The conjugated `S1c = T1c − Z1c·A1c⁻¹·Y1c`. -/
noncomputable def l2S1Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  l2T1Conj H r hr hL q
    - l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹ * l2Y1Conj H r B hB hr hL q

/-- The conjugated bracket `Brc = (1−Kc)·S1c + Z1c·A1c⁻¹·Y1c + Z1c·A1c⁻¹·A0c⁻¹·Y0c·T1c`. -/
noncomputable def l2BrConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  (1 - l2KConj H r B hB hr hL hL2eq q) * l2S1Conj H r B hB hr hL hL2eq q
    + l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹ * l2Y1Conj H r B hB hr hL q
    + l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹
      * l2Y0Conj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q

/-- The conjugated new core block `T1'c = Wc⁻¹·Brc`. -/
noncomputable def l2T1pConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  (l2WConj H r B hB hr hL hL2eq q)⁻¹ * l2BrConj H r B hB hr hL hL2eq q

/-- The conjugated new reg block `Y1'c = Y1c + A0c⁻¹·Y0c·(T1c − T1'c)`. -/
noncomputable def l2Y1pConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  l2Y1Conj H r B hB hr hL q
    + (l2A0Conj H r B hB hr hL q)⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q
      * (l2T1Conj H r hr hL q - l2T1pConj H r B hB hr hL hL2eq q)

/-! ## S0b — the conjugated joint action `psiSplitRawL2CoreConj` + its lens decomposition

`psiSplitRawL2CoreConj` re-encodes the last-layer core block (`T1c ↦ T1'c`) and the last-layer reg
`Y`-tag (`Y1c ↦ Y1'c`) through `paramsEquivFlat`/`regGaugeSlotEquiv`, exactly like the bare
`psiSplitRawL2Core` but with the conjugated `l2T1pConj`/`l2Y1pConj`. Defined directly in terms of the
named blocks so the lens decomposition is `rfl`. -/

/-- The conjugated edited reg/gauge function `g'c` (last-layer `Y`-tag set to `Y1'c`, else `g`). -/
noncomputable def l2g'Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : RegGaugeIdx H r → ℝ := fun idx =>
  match idx with
  | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
      if h : s = lastLayer hL then l2Y1pConj H r B hB hr hL hL2eq q i (h ▸ j)
        else regGaugeSlotEquiv H r hr hL (q.1, q.2.2) idx
  | _ => regGaugeSlotEquiv H r hr hL (q.1, q.2.2) idx

/-- **The conjugated joint `(T1c,Y1c)` action on `DeepestSplit`** (`L = 2`): the bare
`psiSplitRawL2Core` with conjugated pivots/off-diagonals. The core slot updates `lastLayer ↦ T1'c`, the
reg/gauge slot sets the last-layer `Y`-tag to `Y1'c`. -/
noncomputable def psiSplitRawL2CoreConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  let core' : Fin (flatDim (deepestM H r)) → ℝ :=
    paramsEquivFlat (deepestM H r)
      (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1) (lastLayer hL)
        (l2T1pConj H r B hB hr hL hL2eq q))
  let regspec' := (regGaugeSlotEquiv H r hr hL).symm (l2g'Conj H r B hB hr hL hL2eq q)
  (regspec'.1, (core', regspec'.2))

/-- **`psiSplitRawL2CoreConj` IS the encoded triple** in terms of `l2g'Conj`/`l2T1pConj` (`rfl`). -/
theorem psiSplitRawL2CoreConj_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    psiSplitRawL2CoreConj H r B hB hr hL hL2eq q
      = (((regGaugeSlotEquiv H r hr hL).symm (l2g'Conj H r B hB hr hL hL2eq q)).1,
          (paramsEquivFlat (deepestM H r)
            (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1)
              (lastLayer hL) (l2T1pConj H r B hB hr hL hL2eq q)),
          ((regGaugeSlotEquiv H r hr hL).symm (l2g'Conj H r B hB hr hL hL2eq q)).2)) := rfl

/-- The conjugated decoded **core** delta payload: `0` except at the last layer, where it is `T1'c − T1c`. -/
noncomputable def l2CoreΔTupleConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : Params (deepestM H r) :=
  Function.update (0 : Params (deepestM H r)) (lastLayer hL)
    (l2T1pConj H r B hB hr hL hL2eq q - l2T1Conj H r hr hL q)

/-- The conjugated decoded **reg/gauge** delta payload `g'c − g` (nonzero only at the last-layer `Y`-tags). -/
noncomputable def l2GaugeΔConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : RegGaugeIdx H r → ℝ :=
  l2g'Conj H r B hB hr hL hL2eq q - regGaugeSlotEquiv H r hr hL (q.1, q.2.2)

/-- The conjugated core payload encoded by `paramsEquivFlatCLE` is the flat `core'c − q.2.1`
(mirror of `paramsEquivFlatCLE_l2CoreΔTuple_eq`). -/
theorem paramsEquivFlatCLE_l2CoreΔTupleConj_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q)
      = paramsEquivFlat (deepestM H r)
          (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1) (lastLayer hL)
            (l2T1pConj H r B hB hr hL hL2eq q))
        - q.2.1 := by
  let d : Params (deepestM H r) := (paramsEquivFlat (deepestM H r)).symm q.2.1
  let u : Params (deepestM H r) := Function.update d (lastLayer hL) (l2T1pConj H r B hB hr hL hL2eq q)
  have hd_last : d (lastLayer hL) = l2T1Conj H r hr hL q := rfl
  have hΔ : l2CoreΔTupleConj H r B hB hr hL hL2eq q = u - d := by
    funext s
    show l2CoreΔTupleConj H r B hB hr hL hL2eq q s = u s - d s
    rcases eq_or_ne s (lastLayer hL) with h | h
    · subst h
      rw [show u (lastLayer hL) = l2T1pConj H r B hB hr hL hL2eq q from Function.update_self _ _ _,
        hd_last]
      simp only [l2CoreΔTupleConj, Function.update_self]
    · rw [show u s = d s from Function.update_of_ne h _ _, sub_self]
      show l2CoreΔTupleConj H r B hB hr hL hL2eq q s = 0
      rw [l2CoreΔTupleConj, Function.update_of_ne h]; rfl
  rw [hΔ, map_sub, paramsEquivFlatCLE_coe]
  show paramsEquivFlat (deepestM H r) u - paramsEquivFlat (deepestM H r) d
    = paramsEquivFlat (deepestM H r) u - q.2.1
  rw [(paramsEquivFlat (deepestM H r)).apply_symm_apply]

/-- **The conjugated lens decomposition** `psiSplitRawL2CoreConj q − q = (encoded payloads)`
(mirror of `psiSplitDeltaL2Core_eq_payload`): reg/spec slots `regGaugeSlotCLE.symm (l2GaugeΔConj q)`,
core slot `paramsEquivFlatCLE (l2CoreΔTupleConj q)`. -/
theorem psiSplitDeltaL2CoreConj_eq_payload (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q
      = (((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q)).1,
          (paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q),
            ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q)).2)) := by
  have hcore := paramsEquivFlatCLE_l2CoreΔTupleConj_eq H r B hB hr hL hL2eq q
  have hgg : (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q)
      = (regGaugeSlotEquiv H r hr hL).symm (l2g'Conj H r B hB hr hL hL2eq q) - (q.1, q.2.2) := by
    rw [l2GaugeΔConj, map_sub, regGaugeSlotCLE_symm_coe]
    congr 1
    rw [(regGaugeSlotEquiv H r hr hL).symm_apply_apply]
  rw [psiSplitRawL2CoreConj_eq, hcore]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [Prod.fst_sub, hgg, Prod.fst_sub]
  · rfl
  · rw [Prod.snd_sub, Prod.snd_sub, hgg, Prod.snd_sub]

/-! ## S4b — the conjugated named blocks at the split origin

At `q = 0` all reads vanish (`readX/Y/Z_zero`), so `A0c = deepBlkA_0`, `A1c = deepBlkA_last`, and the
off-diagonals collapse to the deepest blocks: `Y0c = deepBlkY_0`, `Z1c = deepBlkZ_last`, `T1c = 0`. At
the L=2 boundary `deepBlkY_0 = 0` (`hY`) and `deepBlkZ_last = 0` (`hZ`), so `Y0c(0) = Z1c(0) = 0` — the
conjugated derivative-vanishing input (mirror of the bare `l2Z1_zero`/`l2Y0_zero`). -/

/-- `Z1c = deepBlkZ_last` at the origin; `= 0` at the L=2 boundary (`hZ`). -/
theorem l2Z1Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    l2Z1Conj H r B hB hr hL 0 = 0 := by
  rw [l2Z1Conj, gaugeProj_zero, readZ_zero H r hr hL, add_zero, hZ]

/-- `Y0c = deepBlkY_0 (cols cast)` at the origin; `= 0` at the L=2 boundary (`hY`). -/
theorem l2Y0Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    l2Y0Conj H r B hB hr hL hL2eq 0 = 0 := by
  rw [l2Y0Conj, gaugeProj_zero, readY_zero H r hr hL, add_zero, hY]
  simp only [Matrix.reindex_apply, Matrix.submatrix_zero, Pi.zero_apply]

/-- `T1c = 0` at the origin (`coreLast 0 = 0`). -/
theorem l2T1Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    l2T1Conj H r hr hL 0 = 0 := l2T1_zero H r hr hL

/-! ## S4b' — the conjugated composite blocks at the origin (`Kc = Rc = 0`, `Wc = 1`)

With `Z1c(0) = 0` (boundary `hZ`), every composite that carries a `Z1c` left factor vanishes at the
origin: `Rc(0) = 0`, `Wc(0) = 1`, `Kc(0) = 0`, and `T1'c(0) − T1c(0) = 0`. The pivots `A0c, A1c` being
deepest blocks (not `1`) is invisible — the vanishing rides on the `Z1c`/`Y0c` factors. -/

/-- `Rc = 0` at the origin (carries `Z1c(0) = 0`). -/
theorem l2RConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    l2RConj H r B hB hr hL hL2eq 0 = 0 := by
  rw [l2RConj, l2Z1Conj_zero H r B hB hr hL hZ]; simp [Matrix.zero_mul]

/-- `Wc = 1` at the origin. -/
theorem l2WConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    l2WConj H r B hB hr hL hL2eq 0 = 1 := by
  rw [l2WConj, l2RConj_zero H r B hB hr hL hL2eq hZ, add_zero]

/-- `Kc = 0` at the origin (carries `Z1c(0) = 0`). -/
theorem l2KConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    l2KConj H r B hB hr hL hL2eq 0 = 0 := by
  rw [l2KConj, l2Z1Conj_zero H r B hB hr hL hZ]; simp [Matrix.zero_mul]

/-! ## S4c — the conjugated `T1'c − T1c` normalization (pure algebra, mirrors `l2Br_sub_T1`)

`T1'c = Wc⁻¹·Brc` and `Brc − T1c = −Kc·S1c + Rc·T1c`, so `T1'c − T1c = (Wc⁻¹ − 1)·Brc + (Brc − T1c)`.
Each summand carries a `Z1c`/`Y0c` factor (`Kc, Rc, Wc⁻¹ − 1` all vanish at the origin), so the strict
derivative at `0` is `0`. Identical algebra to the bare. -/

/-- `T1'c = Wc⁻¹·Brc` (`rfl`). -/
theorem l2T1pConj_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2T1pConj H r B hB hr hL hL2eq q
      = (l2WConj H r B hB hr hL hL2eq q)⁻¹ * l2BrConj H r B hB hr hL hL2eq q := rfl

/-- `Brc − T1c = −(Kc·S1c) + Rc·T1c` (the `±Z1c·A1c⁻¹·Y1c` cancel). -/
theorem l2BrConj_sub_T1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2BrConj H r B hB hr hL hL2eq q - l2T1Conj H r hr hL q
      = -(l2KConj H r B hB hr hL hL2eq q * l2S1Conj H r B hB hr hL hL2eq q)
        + l2RConj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q := by
  rw [l2BrConj, l2S1Conj, l2RConj]
  set Z1 := l2Z1Conj H r B hB hr hL q
  set A1i := (l2A1Conj H r B hB hr hL q)⁻¹
  set A0i := (l2A0Conj H r B hB hr hL q)⁻¹
  set Y0 := l2Y0Conj H r B hB hr hL hL2eq q
  set Y1 := l2Y1Conj H r B hB hr hL q
  set T1 := l2T1Conj H r hr hL q
  set K := l2KConj H r B hB hr hL hL2eq q
  show (1 - K) * (T1 - Z1 * A1i * Y1) + Z1 * A1i * Y1
      + Z1 * A1i * A0i * Y0 * T1 - T1
    = -(K * (T1 - Z1 * A1i * Y1)) + Z1 * A1i * A0i * Y0 * T1
  rw [Matrix.sub_mul, Matrix.one_mul]
  abel

/-- `T1'c − T1c = (Wc⁻¹ − 1)·Brc + (Brc − T1c)`. -/
theorem l2T1pConj_sub_T1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2T1pConj H r B hB hr hL hL2eq q - l2T1Conj H r hr hL q
      = ((l2WConj H r B hB hr hL hL2eq q)⁻¹ - 1) * l2BrConj H r B hB hr hL hL2eq q
        + (l2BrConj H r B hB hr hL hL2eq q - l2T1Conj H r hr hL q) := by
  rw [l2T1pConj_eq]
  set Wi := (l2WConj H r B hB hr hL hL2eq q)⁻¹
  set Br := l2BrConj H r B hB hr hL hL2eq q
  set T1 := l2T1Conj H r hr hL q
  rw [Matrix.sub_mul, Matrix.one_mul]
  abel

/-- `T1'c − T1c = 0` at the origin (`Kc = Rc = 0`, `Wc = 1`, so `Wc⁻¹ − 1 = 0` and `Brc − T1c = 0`). -/
theorem l2T1pConj_sub_T1_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    l2T1pConj H r B hB hr hL hL2eq 0 - l2T1Conj H r hr hL 0 = 0 := by
  rw [l2T1pConj_sub_T1, l2BrConj_sub_T1, l2KConj_zero H r B hB hr hL hL2eq hZ,
    l2RConj_zero H r B hB hr hL hL2eq hZ]
  simp [Matrix.zero_mul, l2WConj_zero H r B hB hr hL hL2eq hZ]

/-! ## S2/S4 — entrywise `ContDiff` of the conjugated blocks (deepBlk const + read)

Each conjugated block entry is `ContDiff ⊤` (the bare's `contDiff_l2·_entry` plus a `deepBlk·` constant
summand). The inverses `(A0c)⁻¹/(A1c)⁻¹/(P00c)⁻¹` are `ContDiffAt` at the origin where the det `≠ 0` —
`det(A0c 0) = det(deepBlkA_0)` (needs `hDA0`), likewise for `A1c`. `P00c(0) = deepBlkA_0·deepBlkA_1`
(boundary `Y0c(0) = 0`), whose det `≠ 0` from both units. -/

/-- Each `l2A0Conj` entry is `ContDiff ⊤`. -/
theorem contDiff_l2A0Conj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2A0Conj H r B hB hr hL q i j) := by
  have : (fun q => l2A0Conj H r B hB hr hL q i j)
      = fun q => deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L) i j
          + readX H r hr hL (q.1, q.2.2) (⟨0, by omega⟩ : Fin L) i j := by
    funext q; rw [l2A0Conj, Matrix.add_apply]
  rw [this]
  exact contDiff_const.add ((contDiff_readX_entry H r hr hL _ i j).comp (contDiff_gaugeProj H r))

/-- Each `l2A1Conj` entry is `ContDiff ⊤`. -/
theorem contDiff_l2A1Conj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2A1Conj H r B hB hr hL q i j) := by
  have : (fun q => l2A1Conj H r B hB hr hL q i j)
      = fun q => deepBlkA H r B hB hr hL (lastLayer hL) i j
          + readX H r hr hL (q.1, q.2.2) (lastLayer hL) i j := by
    funext q; rw [l2A1Conj, Matrix.add_apply]
  rw [this]
  exact contDiff_const.add ((contDiff_readX_entry H r hr hL _ i j).comp (contDiff_gaugeProj H r))

/-- Each `l2Z1Conj` entry is `ContDiff ⊤`. -/
theorem contDiff_l2Z1Conj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Z1Conj H r B hB hr hL q i j) := by
  have : (fun q => l2Z1Conj H r B hB hr hL q i j)
      = fun q => deepBlkZ H r B hB hr hL (lastLayer hL) i j
          + readZ H r hr hL (q.1, q.2.2) (lastLayer hL) i j := by
    funext q; rw [l2Z1Conj, Matrix.add_apply]
  rw [this]
  exact contDiff_const.add ((contDiff_readZ_entry H r hr hL _ i j).comp (contDiff_gaugeProj H r))

/-- Each `l2Y1Conj` entry is `ContDiff ⊤`. -/
theorem contDiff_l2Y1Conj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Y1Conj H r B hB hr hL q i j) := by
  have : (fun q => l2Y1Conj H r B hB hr hL q i j)
      = fun q => deepBlkY H r B hB hr hL (lastLayer hL) i j
          + readY H r hr hL (q.1, q.2.2) (lastLayer hL) i j := by
    funext q; rw [l2Y1Conj, Matrix.add_apply]
  rw [this]
  exact contDiff_const.add ((contDiff_readY_entry H r hr hL _ i j).comp (contDiff_gaugeProj H r))

/-- Each `l2T1Conj` entry is `ContDiff ⊤` (= the bare `l2T1`). -/
theorem contDiff_l2T1Conj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2T1Conj H r hr hL q i j) :=
  contDiff_l2T1_entry H r hr hL i j

/-- Each `l2Y0Conj` entry is `ContDiff ⊤` (deepBlkY const + col-reindexed first-layer `readY`). -/
theorem contDiff_l2Y0Conj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Y0Conj H r B hB hr hL hL2eq q i j) := by
  have : (fun q => l2Y0Conj H r B hB hr hL hL2eq q i j)
      = fun q => deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) i
            ((finCongr (midWidth_eq_of_L2 H r hL hL2eq)).symm j)
          + readY H r hr hL (q.1, q.2.2) (⟨0, by omega⟩ : Fin L) i
            ((finCongr (midWidth_eq_of_L2 H r hL hL2eq)).symm j) := by
    funext q
    rw [l2Y0Conj, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      Matrix.add_apply]
  rw [this]
  exact contDiff_const.add ((contDiff_readY_entry H r hr hL _ i _).comp (contDiff_gaugeProj H r))

/-! ## S2/S4 — the conjugated pivots at the origin + their inverse `ContDiffAt`

`A0c(0) = deepBlkA_0`, `A1c(0) = deepBlkA_last`; with the pivot-base units `hDA0`/`hDA1` their dets are
`≠ 0`, so the inverse entries are `ContDiffAt` at the origin. `P00c(0) = deepBlkA_0·deepBlkA_last`
(boundary `Y0c(0) = 0`), a product of units, hence `det ≠ 0`. -/

/-- `A0c = deepBlkA_0` at the origin. -/
theorem l2A0Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    l2A0Conj H r B hB hr hL 0 = deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L) := by
  rw [l2A0Conj, gaugeProj_zero, readX_zero H r hr hL, add_zero]

/-- `A1c = deepBlkA_last` at the origin. -/
theorem l2A1Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    l2A1Conj H r B hB hr hL 0 = deepBlkA H r B hB hr hL (lastLayer hL) := by
  rw [l2A1Conj, gaugeProj_zero, readX_zero H r hr hL, add_zero]

/-- `P00c = deepBlkA_0·deepBlkA_last` at the origin (`Y0c(0) = 0`, boundary `hY`). -/
theorem l2P00Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    l2P00Conj H r B hB hr hL hL2eq 0
      = deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L) * deepBlkA H r B hB hr hL (lastLayer hL) := by
  rw [l2P00Conj, l2A0Conj_zero, l2A1Conj_zero, l2Y0Conj_zero H r B hB hr hL hL2eq hY,
    Matrix.zero_mul, add_zero]

/-- The pivot-base unit `hDA0` gives `det(A0c 0) ≠ 0`. -/
theorem l2A0Conj_det_ne_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L))) :
    (l2A0Conj H r B hB hr hL 0).det ≠ 0 := by
  rw [l2A0Conj_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hDA0).ne_zero

/-- The pivot-base unit `hDA1` gives `det(A1c 0) ≠ 0`. -/
theorem l2A1Conj_det_ne_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL))) :
    (l2A1Conj H r B hB hr hL 0).det ≠ 0 := by
  rw [l2A1Conj_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hDA1).ne_zero

/-- `det(P00c 0) ≠ 0` (product of the two pivot-base units). -/
theorem l2P00Conj_det_ne_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    (l2P00Conj H r B hB hr hL hL2eq 0).det ≠ 0 := by
  rw [l2P00Conj_zero H r B hB hr hL hL2eq hY, Matrix.det_mul]
  exact mul_ne_zero (((Matrix.isUnit_iff_isUnit_det _).mp hDA0).ne_zero)
    (((Matrix.isUnit_iff_isUnit_det _).mp hDA1).ne_zero)

/-- `(A0c)⁻¹` entries `ContDiffAt` at the origin (`hDA0`). -/
theorem contDiffAt_l2A0Conjinv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L))) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2A0Conj H r B hB hr hL q)⁻¹ i j) 0 :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => (contDiff_l2A0Conj_entry H r B hB hr hL a b).contDiffAt)
    (l2A0Conj_det_ne_zero H r B hB hr hL hDA0) i j

/-- `(A1c)⁻¹` entries `ContDiffAt` at the origin (`hDA1`). -/
theorem contDiffAt_l2A1Conjinv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL))) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2A1Conj H r B hB hr hL q)⁻¹ i j) 0 :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => (contDiff_l2A1Conj_entry H r B hB hr hL a b).contDiffAt)
    (l2A1Conj_det_ne_zero H r B hB hr hL hDA1) i j

/-- `(P00c)⁻¹` entries `ContDiffAt` at the origin (`hDA0`, `hDA1`, `hY`). -/
theorem contDiffAt_l2P00Conjinv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2P00Conj H r B hB hr hL hL2eq q)⁻¹ i j) 0 := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero_at (fun a b => ?_)
    (l2P00Conj_det_ne_zero H r B hB hr hL hL2eq hDA0 hDA1 hY) i j
  have hpe : (fun q => l2P00Conj H r B hB hr hL hL2eq q a b)
      = fun q => (l2A0Conj H r B hB hr hL q * l2A1Conj H r B hB hr hL q) a b
        + (l2Y0Conj H r B hB hr hL hL2eq q * l2Z1Conj H r B hB hr hL q) a b := by
    funext q; rw [l2P00Conj, Matrix.add_apply]
  rw [hpe]
  exact (contDiffAt_matrix_mul_entry
      (fun a' k => (contDiff_l2A0Conj_entry H r B hB hr hL a' k).contDiffAt)
      (fun k b' => (contDiff_l2A1Conj_entry H r B hB hr hL k b').contDiffAt) a b).add
    (contDiffAt_matrix_mul_entry
      (fun a' k => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq a' k).contDiffAt)
      (fun k b' => (contDiff_l2Z1Conj_entry H r B hB hr hL k b').contDiffAt) a b)

/-- `(A1c⁻¹·A0c⁻¹)` entries `ContDiffAt` at the origin (`hDA0`, `hDA1`). -/
theorem contDiffAt_l2A1invA0invConj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL))) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => ((l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹) i j) 0 :=
  contDiffAt_matrix_mul_entry (fun a k => contDiffAt_l2A1Conjinv_entry H r B hB hr hL hDA1 a k)
    (fun k b => contDiffAt_l2A0Conjinv_entry H r B hB hr hL hDA0 k b) i j

end DLNFibre.DLN.RLCT
