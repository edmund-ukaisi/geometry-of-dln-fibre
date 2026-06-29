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

/-- The conjugated new last-layer reg **READ** `readY_last + A0c⁻¹·Y0c·(T1c − T1'c)` (`= Y1'c −
deepBlkY_last`). The gauge slot stores READS, and the conjugated last-Y block is `Y1c = deepBlkY_last +
readY_last`; so the move WRITES this read so that the post-move conjugated block IS `Y1'c` (genm-l2thread
CONFIRMED, load-bearing: literal `Y1'c` would break the basepoint, `deepBlkY_last ≠ 0`). Contrast the
CORE: `T1'c` is written LITERALLY (no offset) since `deepBlkT_last = 0`, so there the read IS the block. -/
noncomputable def l2Y1pReadConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  readY H r hr hL (q.1, q.2.2) (lastLayer hL)
    + (l2A0Conj H r B hB hr hL q)⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q
      * (l2T1Conj H r hr hL q - l2T1pConj H r B hB hr hL hL2eq q)

/-- The new read minus the old read is the SAME delta as `Y1'c − Y1c` (the deepest constant cancels):
`l2Y1pReadConj − readY_last = l2Y1pConj − l2Y1Conj`. So all derivative/ContDiffAt facts stated via the
`l2Y1pConj − l2Y1Conj` delta transfer verbatim to the read-encode. -/
theorem l2Y1pReadConj_sub_read_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2Y1pReadConj H r B hB hr hL hL2eq q - readY H r hr hL (q.1, q.2.2) (lastLayer hL)
      = l2Y1pConj H r B hB hr hL hL2eq q - l2Y1Conj H r B hB hr hL q := by
  rw [l2Y1pReadConj, l2Y1pConj, l2Y1Conj]; abel

/-! ## S0b — the conjugated joint action `psiSplitRawL2CoreConj` + its lens decomposition

`psiSplitRawL2CoreConj` re-encodes the last-layer core block (`T1c ↦ T1'c`) and the last-layer reg
`Y`-tag (`Y1c ↦ Y1'c`) through `paramsEquivFlat`/`regGaugeSlotEquiv`, exactly like the bare
`psiSplitRawL2Core` but with the conjugated `l2T1pConj`/`l2Y1pConj`. Defined directly in terms of the
named blocks so the lens decomposition is `rfl`. -/

/-- The conjugated edited reg/gauge function `g'c` (last-layer `Y`-tag set to the new READ
`l2Y1pReadConj`, else `g`). The gauge slot stores reads, so the move writes `Y1'c − deepBlkY_last`. -/
noncomputable def l2g'Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : RegGaugeIdx H r → ℝ := fun idx =>
  match idx with
  | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
      if h : s = lastLayer hL then l2Y1pReadConj H r B hB hr hL hL2eq q i (h ▸ j)
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

/-- `l2Y1pReadConj = 0` at the split origin (`readY_last(0) = 0`, `Y0c(0) = 0` boundary). -/
theorem l2Y1pReadConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    l2Y1pReadConj H r B hB hr hL hL2eq 0 = 0 := by
  rw [l2Y1pReadConj, l2Y0Conj_zero H r B hB hr hL hL2eq hY, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    gaugeProj_zero, readY_zero H r hr hL]

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

/-! ## S2/S4 — the conjugated composite `ContDiffAt` (R, S1, Br) at the origin

Mirror the bare `contDiffAt_l2R_entry`/`_l2S1_entry`/`_l2Br_entry`, threading the conjugated inverse
`ContDiffAt` (which carry `hDA0`/`hDA1`/`hY`). -/

/-- `Rc` entries `ContDiffAt` at the origin. -/
theorem contDiffAt_l2RConj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2RConj H r B hB hr hL hL2eq q i j) 0 := by
  have heq : (fun q => l2RConj H r B hB hr hL hL2eq q i j)
      = fun q => (l2Z1Conj H r B hB hr hL q
          * ((l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹)
          * l2Y0Conj H r B hB hr hL hL2eq q) i j := by
    funext q
    have hassoc : l2RConj H r B hB hr hL hL2eq q
        = l2Z1Conj H r B hB hr hL q
          * ((l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹)
          * l2Y0Conj H r B hB hr hL hL2eq q := by
      rw [l2RConj, Matrix.mul_assoc (l2Z1Conj H r B hB hr hL q) (l2A1Conj H r B hB hr hL q)⁻¹
        (l2A0Conj H r B hB hr hL q)⁻¹]
    rw [hassoc]
  rw [heq]
  refine contDiffAt_matrix_mul_entry (A := fun q => l2Z1Conj H r B hB hr hL q
      * ((l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹)) ?_
    (fun k b => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq k b).contDiffAt) i j
  intro a k
  exact contDiffAt_matrix_mul_entry
    (fun a' k' => (contDiff_l2Z1Conj_entry H r B hB hr hL a' k').contDiffAt)
    (fun k' b' => contDiffAt_l2A1invA0invConj_entry H r B hB hr hL hDA0 hDA1 k' b') a k

/-- `Wc` entries `ContDiffAt` at the origin (`1 + Rc`). -/
theorem contDiffAt_l2WConj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2WConj H r B hB hr hL hL2eq q i j) 0 := by
  have heq : (fun q => l2WConj H r B hB hr hL hL2eq q i j)
      = fun q => (1 : Matrix _ _ ℝ) i j + l2RConj H r B hB hr hL hL2eq q i j := by
    funext q; rw [l2WConj, Matrix.add_apply]
  rw [heq]; exact contDiffAt_const.add (contDiffAt_l2RConj_entry H r B hB hr hL hL2eq hDA0 hDA1 i j)

/-- `S1c` entries `ContDiffAt` at the origin. -/
theorem contDiffAt_l2S1Conj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2S1Conj H r B hB hr hL hL2eq q i j) 0 := by
  have heq : (fun q => l2S1Conj H r B hB hr hL hL2eq q i j)
      = fun q => l2T1Conj H r hr hL q i j
          - (l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹
              * l2Y1Conj H r B hB hr hL q) i j := by
    funext q; rw [l2S1Conj, Matrix.sub_apply]
  rw [heq]
  refine (contDiff_l2T1Conj_entry H r hr hL i j).contDiffAt.sub ?_
  refine contDiffAt_matrix_mul_entry
    (A := fun q => l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹) ?_
    (fun k b => (contDiff_l2Y1Conj_entry H r B hB hr hL k b).contDiffAt) i j
  intro a k
  exact contDiffAt_matrix_mul_entry
    (fun a' k' => (contDiff_l2Z1Conj_entry H r B hB hr hL a' k').contDiffAt)
    (fun k' b' => contDiffAt_l2A1Conjinv_entry H r B hB hr hL hDA1 k' b') a k

/-- `Brc` entries `ContDiffAt` at the origin (the three-summand bracket). -/
theorem contDiffAt_l2BrConj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2BrConj H r B hB hr hL hL2eq q i j) 0 := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2KConj H r B hB hr hL hL2eq q)
          * l2S1Conj H r B hB hr hL hL2eq q) i j) 0 := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
        (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2KConj H r B hB hr hL hL2eq q) ?_
      (fun k b => contDiffAt_l2S1Conj_entry H r B hB hr hL hL2eq hDA1 k b) i j
    intro a k
    have hsub : (fun q => (1 - l2KConj H r B hB hr hL hL2eq q) a k)
        = fun q => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) a k
            - l2KConj H r B hB hr hL hL2eq q a k := by
      funext q; rw [Matrix.sub_apply]
    rw [hsub]
    refine contDiffAt_const.sub ?_
    have hKeq : (fun q => l2KConj H r B hB hr hL hL2eq q a k)
        = fun q => (l2Z1Conj H r B hB hr hL q * (l2P00Conj H r B hB hr hL hL2eq q)⁻¹
            * l2Y0Conj H r B hB hr hL hL2eq q) a k := by
      funext q; rw [l2KConj]
    rw [hKeq]
    refine contDiffAt_matrix_mul_entry
      (A := fun q => l2Z1Conj H r B hB hr hL q * (l2P00Conj H r B hB hr hL hL2eq q)⁻¹) ?_
      (fun k' b' => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq k' b').contDiffAt) a k
    intro a' k'
    exact contDiffAt_matrix_mul_entry
      (fun a'' k'' => (contDiff_l2Z1Conj_entry H r B hB hr hL a'' k'').contDiffAt)
      (fun k'' b'' => contDiffAt_l2P00Conjinv_entry H r B hB hr hL hL2eq hDA0 hDA1 hY k'' b'') a' k'
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹
          * l2Y1Conj H r B hB hr hL q) i j) 0 := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q => l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹) ?_
      (fun k b => (contDiff_l2Y1Conj_entry H r B hB hr hL k b).contDiffAt) i j
    intro a k
    exact contDiffAt_matrix_mul_entry
      (fun a' k' => (contDiff_l2Z1Conj_entry H r B hB hr hL a' k').contDiffAt)
      (fun k' b' => contDiffAt_l2A1Conjinv_entry H r B hB hr hL hDA1 k' b') a k
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹
          * l2Y0Conj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q) i j) 0 := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q => l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹
          * (l2A0Conj H r B hB hr hL q)⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q) ?_
      (fun k b => (contDiff_l2T1Conj_entry H r hr hL k b).contDiffAt) i j
    intro a k
    refine contDiffAt_matrix_mul_entry
      (A := fun q => l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹
          * (l2A0Conj H r B hB hr hL q)⁻¹) ?_
      (fun k' b' => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq k' b').contDiffAt) a k
    intro a' k'
    refine contDiffAt_matrix_mul_entry
      (A := fun q => l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹) ?_
      (fun k'' b'' => contDiffAt_l2A0Conjinv_entry H r B hB hr hL hDA0 k'' b'') a' k'
    intro a'' k''
    exact contDiffAt_matrix_mul_entry
      (fun a3 k3 => (contDiff_l2Z1Conj_entry H r B hB hr hL a3 k3).contDiffAt)
      (fun k3 b3 => contDiffAt_l2A1Conjinv_entry H r B hB hr hL hDA1 k3 b3) a'' k''
  have heq : (fun q => l2BrConj H r B hB hr hL hL2eq q i j)
      = fun q => (((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2KConj H r B hB hr hL hL2eq q)
          * l2S1Conj H r B hB hr hL hL2eq q) i j
          + (l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹
              * l2Y1Conj H r B hB hr hL q) i j
          + (l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹
              * l2Y0Conj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q) i j := by
    funext q; rw [l2BrConj, Matrix.add_apply, Matrix.add_apply]
  rw [heq]
  exact (h1.add h2).add h3

/-! ## S4 — the conjugated strict-derivative-`0` chain

Mirror the bare `hasStrictFDerivAt_l2{K,R,Winv_sub_one,T1p_sub_T1,Y1p_sub_Y1}_entry_zero`. Each carries
a `Z1c`/`Y0c` outer factor that vanishes at the origin (boundary), so the entry strict derivative is
`0`. The inverse-bearing pieces thread `hDA0`/`hDA1`/`hY`. -/

/-- `Kc` entry strict-deriv `0` at the origin (`Z1c`, `Y0c` outer factors vanish). -/
theorem hasStrictFDerivAt_l2KConj_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => l2KConj H r B hB hr hL hL2eq q i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have heq : (fun q => l2KConj H r B hB hr hL hL2eq q i j)
      = fun q => (l2Z1Conj H r B hB hr hL q * (l2P00Conj H r B hB hr hL hL2eq q)⁻¹
          * l2Y0Conj H r B hB hr hL hL2eq q) i j := by
    funext q; rw [l2KConj]
  rw [heq]
  refine hasStrictFDerivAt_matrix_triple_mul_entry_zero
    (A := fun q => l2Z1Conj H r B hB hr hL q)
    (B := fun q => (l2P00Conj H r B hB hr hL hL2eq q)⁻¹)
    (C := fun q => l2Y0Conj H r B hB hr hL hL2eq q) i j
    (fun a b => (contDiff_l2Z1Conj_entry H r B hB hr hL a b).contDiffAt)
    (fun a b => contDiffAt_l2P00Conjinv_entry H r B hB hr hL hL2eq hDA0 hDA1 hY a b)
    (fun a b => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq a b).contDiffAt) ?_ ?_
  · intro a b; simp only [l2Z1Conj_zero H r B hB hr hL hZ, Matrix.zero_apply]
  · intro a b; simp only [l2Y0Conj_zero H r B hB hr hL hL2eq hY, Matrix.zero_apply]

/-- `Rc` entry strict-deriv `0` at the origin. -/
theorem hasStrictFDerivAt_l2RConj_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => l2RConj H r B hB hr hL hL2eq q i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have heq : (fun q => l2RConj H r B hB hr hL hL2eq q i j)
      = fun q => (l2Z1Conj H r B hB hr hL q
          * ((l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹)
          * l2Y0Conj H r B hB hr hL hL2eq q) i j := by
    funext q
    have hassoc : l2RConj H r B hB hr hL hL2eq q
        = l2Z1Conj H r B hB hr hL q
          * ((l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹)
          * l2Y0Conj H r B hB hr hL hL2eq q := by
      rw [l2RConj, Matrix.mul_assoc (l2Z1Conj H r B hB hr hL q) (l2A1Conj H r B hB hr hL q)⁻¹
        (l2A0Conj H r B hB hr hL q)⁻¹]
    rw [hassoc]
  rw [heq]
  refine hasStrictFDerivAt_matrix_triple_mul_entry_zero
    (A := fun q => l2Z1Conj H r B hB hr hL q)
    (B := fun q => (l2A1Conj H r B hB hr hL q)⁻¹ * (l2A0Conj H r B hB hr hL q)⁻¹)
    (C := fun q => l2Y0Conj H r B hB hr hL hL2eq q) i j
    (fun a b => (contDiff_l2Z1Conj_entry H r B hB hr hL a b).contDiffAt)
    (fun a b => contDiffAt_l2A1invA0invConj_entry H r B hB hr hL hDA0 hDA1 a b)
    (fun a b => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq a b).contDiffAt) ?_ ?_
  · intro a b; simp only [l2Z1Conj_zero H r B hB hr hL hZ, Matrix.zero_apply]
  · intro a b; simp only [l2Y0Conj_zero H r B hB hr hL hL2eq hY, Matrix.zero_apply]

/-- `(Wc − 1) i j = Rc i j` (pointwise). -/
theorem l2WConj_sub_one_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    (l2WConj H r B hB hr hL hL2eq q - 1) i j = l2RConj H r B hB hr hL hL2eq q i j := by
  rw [l2WConj]; simp [Matrix.add_apply, Matrix.sub_apply]

/-- `(Wc⁻¹ − 1) i j = 0` at the origin. -/
theorem l2WConjinv_sub_one_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ((l2WConj H r B hB hr hL hL2eq 0)⁻¹ - 1) i j = 0 := by
  rw [l2WConj_zero H r B hB hr hL hL2eq hZ, inv_one]; simp [Matrix.sub_apply]

/-- `(Wc⁻¹ − 1)` entry strict-deriv `0` at the origin (via the generic keystone; `Wc − 1 = Rc`). -/
theorem hasStrictFDerivAt_l2WConjinv_sub_one_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => ((l2WConj H r B hB hr hL hL2eq q)⁻¹ - 1) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  refine hasStrictFDerivAt_winv_sub_one_entry_zero (W := l2WConj H r B hB hr hL hL2eq) i j
    (fun a b => contDiffAt_l2WConj_entry H r B hB hr hL hL2eq hDA0 hDA1 a b) ?_ ?_ ?_
  · rw [l2WConj_zero H r B hB hr hL hL2eq hZ, Matrix.det_one]; exact one_ne_zero
  · intro a b
    refine (hasStrictFDerivAt_l2RConj_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ a b).congr_of_eventuallyEq ?_
    filter_upwards with q
    rw [l2WConj_sub_one_apply]
  · intro a b; rw [l2WConj_sub_one_apply, l2RConj_zero H r B hB hr hL hL2eq hZ]; rfl

/-- `(T1'c − T1c)` entry strict-deriv `0` at the origin. -/
theorem hasStrictFDerivAt_l2T1pConj_sub_T1_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt (fun q => (l2T1pConj H r B hB hr hL hL2eq q - l2T1Conj H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have heq : (fun q => (l2T1pConj H r B hB hr hL hL2eq q - l2T1Conj H r hr hL q) i j)
      = fun q => (((l2WConj H r B hB hr hL hL2eq q)⁻¹
            - (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
              (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ)) * l2BrConj H r B hB hr hL hL2eq q) i j
          + (-(l2KConj H r B hB hr hL hL2eq q * l2S1Conj H r B hB hr hL hL2eq q)
              + l2RConj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q) i j := by
    funext q
    rw [l2T1pConj_sub_T1, l2BrConj_sub_T1, Matrix.add_apply]
  rw [heq]
  have hP1 : HasStrictFDerivAt
      (fun q => (((l2WConj H r B hB hr hL hL2eq q)⁻¹
          - (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ)) * l2BrConj H r B hB hr hL hL2eq q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_mul_entry_of_left_zero i j
      (fun k => hasStrictFDerivAt_l2WConjinv_sub_one_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ i k)
      (fun k => l2WConjinv_sub_one_zero H r B hB hr hL hL2eq hZ i k)
      (fun k => contDiffAt_l2BrConj_entry H r B hB hr hL hL2eq hDA0 hDA1 hY k j)
  have hKS1 : HasStrictFDerivAt
      (fun q => (l2KConj H r B hB hr hL hL2eq q * l2S1Conj H r B hB hr hL hL2eq q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_mul_entry_of_left_zero i j
      (fun k => hasStrictFDerivAt_l2KConj_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ i k)
      (fun k => by rw [l2KConj_zero H r B hB hr hL hL2eq hZ]; simp)
      (fun k => contDiffAt_l2S1Conj_entry H r B hB hr hL hL2eq hDA1 k j)
  have hRT1 : HasStrictFDerivAt
      (fun q => (l2RConj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_mul_entry_of_left_zero i j
      (fun k => hasStrictFDerivAt_l2RConj_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ i k)
      (fun k => by rw [l2RConj_zero H r B hB hr hL hL2eq hZ]; simp)
      (fun k => (contDiff_l2T1Conj_entry H r hr hL k j).contDiffAt)
  have hP2 : HasStrictFDerivAt
      (fun q => (-(l2KConj H r B hB hr hL hL2eq q * l2S1Conj H r B hB hr hL hL2eq q)
          + l2RConj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
    have hsum := (hKS1.neg).add hRT1
    rw [neg_zero, add_zero] at hsum
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards with q
    simp only [Matrix.add_apply, Matrix.neg_apply, Pi.add_apply, Pi.neg_apply]
  have hadd := hP1.add hP2
  simpa using hadd

/-! ## S4 — the conjugated reg payload `Y1'c − Y1c` + the encoded core/gauge payloads -/

/-- `(T1c − T1'c)` entry strict-deriv `0` (negation of `T1'c − T1c`). -/
theorem hasStrictFDerivAt_l2T1Conj_sub_T1p_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt (fun q => (l2T1Conj H r hr hL q - l2T1pConj H r B hB hr hL hL2eq q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have hneg := (hasStrictFDerivAt_l2T1pConj_sub_T1_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ i j).neg
  simp only [neg_zero] at hneg
  refine hneg.congr_of_eventuallyEq ?_
  filter_upwards with q
  simp only [Pi.neg_apply, Matrix.sub_apply]; ring

/-- `(T1c − T1'c) i j = 0` at the origin. -/
theorem l2T1Conj_sub_T1p_zero_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    (l2T1Conj H r hr hL 0 - l2T1pConj H r B hB hr hL hL2eq 0) i j = 0 := by
  have h0 := l2T1pConj_sub_T1_zero H r B hB hr hL hL2eq hZ
  have : l2T1Conj H r hr hL 0 - l2T1pConj H r B hB hr hL hL2eq 0 = 0 := by
    rw [← neg_sub, h0, neg_zero]
  rw [this]; rfl

/-- `(A0c⁻¹·Y0c)` entries `ContDiffAt` at the origin. -/
theorem contDiffAt_l2A0invY0Conj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => ((l2A0Conj H r B hB hr hL q)⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q) i j) 0 :=
  contDiffAt_matrix_mul_entry (fun a k => contDiffAt_l2A0Conjinv_entry H r B hB hr hL hDA0 a k)
    (fun k b => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq k b).contDiffAt) i j

/-- `Y1'c − Y1c = A0c⁻¹·Y0c·(T1c − T1'c)` (pure algebra). -/
theorem l2Y1pConj_sub_Y1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2Y1pConj H r B hB hr hL hL2eq q - l2Y1Conj H r B hB hr hL q
      = (l2A0Conj H r B hB hr hL q)⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q
          * (l2T1Conj H r hr hL q - l2T1pConj H r B hB hr hL hL2eq q) := by
  rw [l2Y1pConj]; abel

/-- `(Y1'c − Y1c)` entry strict-deriv `0` (= `A0c⁻¹·Y0c·(T1c − T1'c)`, right factor vanishes). -/
theorem hasStrictFDerivAt_l2Y1pConj_sub_Y1_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt (fun q => (l2Y1pConj H r B hB hr hL hL2eq q - l2Y1Conj H r B hB hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have heq : (fun q => (l2Y1pConj H r B hB hr hL hL2eq q - l2Y1Conj H r B hB hr hL q) i j)
      = fun q => (((l2A0Conj H r B hB hr hL q)⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q)
          * (l2T1Conj H r hr hL q - l2T1pConj H r B hB hr hL hL2eq q)) i j := by
    funext q; rw [l2Y1pConj_sub_Y1, Matrix.mul_assoc]
  rw [heq]
  exact hasStrictFDerivAt_matrix_mul_entry_of_right_zero i j
    (fun k => contDiffAt_l2A0invY0Conj_entry H r B hB hr hL hL2eq hDA0 i k)
    (fun k => hasStrictFDerivAt_l2T1Conj_sub_T1p_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ k j)
    (fun k => l2T1Conj_sub_T1p_zero_entry H r B hB hr hL hL2eq hZ k j)

/-- The conjugated gauge payload `l2GaugeΔConj` has strict-deriv `0` at the origin
(only the last-layer `Y`-tags are nonzero, where it is `Y1'c − Y1c`). -/
theorem hasStrictFDerivAt_l2GaugeΔConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    HasStrictFDerivAt (l2GaugeΔConj H r B hB hr hL hL2eq)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (RegGaugeIdx H r → ℝ)) 0 := by
  refine hasStrictFDerivAt_pi'.2 (fun idx => ?_)
  rw [ContinuousLinearMap.comp_zero]
  obtain ⟨s, rest⟩ := idx
  rcases rest with (rest | rest)
  · rcases rest with rest | ⟨i, j⟩
    · have h0 : (fun q => l2GaugeΔConj H r B hB hr hL hL2eq q ⟨s, Sum.inl (Sum.inl rest)⟩)
          = fun _ => (0 : ℝ) := by
        funext q; simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply]; ring
      rw [h0]; exact hasStrictFDerivAt_const _ _
    · by_cases h : s = lastLayer hL
      · subst h
        -- The payload at the last-`Y` tag is the NEW read minus the OLD read, exactly the delta
        -- `l2Y1pConj − l2Y1Conj` (the deepest constant cancels — `l2Y1pReadConj_sub_read_eq`).
        have hY' : (fun q => l2GaugeΔConj H r B hB hr hL hL2eq q
              ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩)
            = fun q => (l2Y1pConj H r B hB hr hL hL2eq q - l2Y1Conj H r B hB hr hL q) i j := by
          funext q
          have hg : regGaugeSlotEquiv H r hr hL (q.1, q.2.2)
              ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩
              = readY H r hr hL (q.1, q.2.2) (lastLayer hL) i j := rfl
          simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply, dif_pos, hg]
          have := congrFun (congrFun (l2Y1pReadConj_sub_read_eq H r B hB hr hL hL2eq q) i) j
          rw [Matrix.sub_apply, Matrix.sub_apply] at this
          exact this
        rw [hY']
        exact hasStrictFDerivAt_l2Y1pConj_sub_Y1_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ i j
      · have h0 : (fun q => l2GaugeΔConj H r B hB hr hL hL2eq q ⟨s, Sum.inl (Sum.inr (i, j))⟩)
            = fun _ => (0 : ℝ) := by
          funext q; simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply, dif_neg h]; ring
        rw [h0]; exact hasStrictFDerivAt_const _ _
  · have h0 : (fun q => l2GaugeΔConj H r B hB hr hL hL2eq q ⟨s, Sum.inr rest⟩)
        = fun _ => (0 : ℝ) := by
      funext q; simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply]; ring
    rw [h0]; exact hasStrictFDerivAt_const _ _

/-- The conjugated core payload entry `l2CoreΔTupleConj q s i j` has strict-deriv `0` at the origin. -/
theorem hasStrictFDerivAt_l2CoreΔTupleConj_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (s : Fin L) (i : Fin (deepestM H r s.castSucc)) (j : Fin (deepestM H r s.succ)) :
    HasStrictFDerivAt (fun q => l2CoreΔTupleConj H r B hB hr hL hL2eq q s i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  rcases eq_or_ne s (lastLayer hL) with hs | hs
  · subst hs
    have hentry : (fun q => l2CoreΔTupleConj H r B hB hr hL hL2eq q (lastLayer hL) i j)
        = fun q => (l2T1pConj H r B hB hr hL hL2eq q - l2T1Conj H r hr hL q) i j := by
      funext q; rw [l2CoreΔTupleConj, Function.update_self]
    rw [hentry]
    exact hasStrictFDerivAt_l2T1pConj_sub_T1_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ i j
  · have hentry : (fun q => l2CoreΔTupleConj H r B hB hr hL hL2eq q s i j) = fun _ => (0 : ℝ) := by
      funext q; rw [l2CoreΔTupleConj, Function.update_of_ne hs]; rfl
    rw [hentry]; exact hasStrictFDerivAt_const _ _

/-- The encoded conjugated core payload `paramsEquivFlatCLE (l2CoreΔTupleConj q)` has strict-deriv `0`. -/
theorem hasStrictFDerivAt_paramsEquivFlatCLE_l2CoreΔTupleConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    HasStrictFDerivAt
      (fun q => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (flatDim (deepestM H r)) → ℝ)) 0 := by
  refine hasStrictFDerivAt_pi'.2 (fun k => ?_)
  rw [ContinuousLinearMap.comp_zero]
  set d := (Fintype.equivFin (FlatIdx (deepestM H r))).symm k with hd
  have hcoord : (fun q => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q) k)
      = fun q => l2CoreΔTupleConj H r B hB hr hL hL2eq q d.1.1 d.1.2 d.2 := by
    funext q
    rw [show (⇑(paramsEquivFlatCLE (deepestM H r)) : Params (deepestM H r) → _)
        = ⇑(paramsEquivFlat (deepestM H r)) from paramsEquivFlatCLE_coe (deepestM H r)]
    rfl
  rw [hcoord]
  exact hasStrictFDerivAt_l2CoreΔTupleConj_entry_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ d.1.1 d.1.2 d.2

/-- **S4 — the conjugated joint correction has strict derivative `0` at the split origin**
(`psiSplitRawL2CoreConj q − q`), via the lens decomposition: both encoded payloads have strict-deriv
`0`. The conjugated analogue of `hasStrictFDerivAt_psiSplitDeltaL2Core_zero`. -/
theorem hasStrictFDerivAt_psiSplitDeltaL2CoreConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    HasStrictFDerivAt (fun q => psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0 := by
  have heq : (fun q => psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q)
      = fun q => (((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q)).1,
          (paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q),
            ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q)).2)) := by
    funext q; exact psiSplitDeltaL2CoreConj_eq_payload H r B hB hr hL hL2eq q
  rw [heq]
  have hrg : HasStrictFDerivAt
      (fun q => (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
        ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))) 0 := by
    have hcle := ((regGaugeSlotCLE H r hr hL).symm.toContinuousLinearMap).hasStrictFDerivAt
      (x := l2GaugeΔConj H r B hB hr hL hL2eq 0)
    have hcomp := hcle.comp 0 (hasStrictFDerivAt_l2GaugeΔConj_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ)
    simpa using hcomp
  have hcore := hasStrictFDerivAt_paramsEquivFlatCLE_l2CoreΔTupleConj_zero H r B hB hr hL hL2eq
    hDA0 hDA1 hY hZ
  have h1 : HasStrictFDerivAt
      (fun q => ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q)).1)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 := by
    have := (ContinuousLinearMap.fst ℝ (Fin (deepestNReg H r) → ℝ)
      (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt.comp 0 hrg
    simpa using this
  have h3 : HasStrictFDerivAt
      (fun q => ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q)).2)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNGauge H r) → ℝ)) 0 := by
    have := (ContinuousLinearMap.snd ℝ (Fin (deepestNReg H r) → ℝ)
      (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt.comp 0 hrg
    simpa using this
  exact h1.prodMk (hcore.prodMk h3)

/-! ## S2 — the conjugated `ContDiffAt`-at-arbitrary-`q` chain (the cutoff-support smoothness)

For the global ContDiff of the cutoff map, the raw correction must be `ContDiffAt` at every support
point `q` where the four conjugated dets `det(A0c q), det(A1c q), det(P00c q), det(Wc q)` are `≠ 0`.
These mirror the bare `_at` chain, taking the dets as raw hypotheses (so `hDA` is NOT needed here — the
det-`≠ 0` conditions come from the cutoff support, decoupled from the pivot-base units). -/

/-- `(A0c)⁻¹` entries `ContDiffAt` at `q` (`det(A0c q) ≠ 0`). -/
theorem contDiffAt_l2A0Conjinv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) (hdet : (l2A0Conj H r B hB hr hL q).det ≠ 0)
    (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => (l2A0Conj H r B hB hr hL q')⁻¹ i j) q :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => (contDiff_l2A0Conj_entry H r B hB hr hL a b).contDiffAt) hdet i j

/-- `(A1c)⁻¹` entries `ContDiffAt` at `q`. -/
theorem contDiffAt_l2A1Conjinv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) (hdet : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => (l2A1Conj H r B hB hr hL q')⁻¹ i j) q :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => (contDiff_l2A1Conj_entry H r B hB hr hL a b).contDiffAt) hdet i j

/-- `(P00c)⁻¹` entries `ContDiffAt` at `q`. -/
theorem contDiffAt_l2P00Conjinv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hdet : (l2P00Conj H r B hB hr hL hL2eq q).det ≠ 0)
    (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => (l2P00Conj H r B hB hr hL hL2eq q')⁻¹ i j) q := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero_at (fun a b => ?_) hdet i j
  have hpe : (fun q' => l2P00Conj H r B hB hr hL hL2eq q' a b)
      = fun q' => (l2A0Conj H r B hB hr hL q' * l2A1Conj H r B hB hr hL q') a b
        + (l2Y0Conj H r B hB hr hL hL2eq q' * l2Z1Conj H r B hB hr hL q') a b := by
    funext q'; rw [l2P00Conj, Matrix.add_apply]
  rw [hpe]
  exact (contDiffAt_matrix_mul_entry
      (fun a' k => (contDiff_l2A0Conj_entry H r B hB hr hL a' k).contDiffAt)
      (fun k b' => (contDiff_l2A1Conj_entry H r B hB hr hL k b').contDiffAt) a b).add
    (contDiffAt_matrix_mul_entry
      (fun a' k => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq a' k).contDiffAt)
      (fun k b' => (contDiff_l2Z1Conj_entry H r B hB hr hL k b').contDiffAt) a b)

/-- `Wc` entries `ContDiffAt` at `q` (`det A0c, A1c ≠ 0`). -/
theorem contDiffAt_l2WConj_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0Conj H r B hB hr hL q).det ≠ 0) (hA1 : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2WConj H r B hB hr hL hL2eq q' i j) q := by
  have heq : (fun q' => l2WConj H r B hB hr hL hL2eq q' i j)
      = fun q' => (1 : Matrix _ _ ℝ) i j + l2RConj H r B hB hr hL hL2eq q' i j := by
    funext q'; rw [l2WConj, Matrix.add_apply]
  rw [heq]
  refine contDiffAt_const.add ?_
  have hRe : (fun q' => l2RConj H r B hB hr hL hL2eq q' i j)
      = fun q' => (l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹
          * (l2A0Conj H r B hB hr hL q')⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q') i j := by
    funext q'; rw [l2RConj]
  rw [hRe]
  refine contDiffAt_matrix_mul_entry
    (A := fun q' => l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹
        * (l2A0Conj H r B hB hr hL q')⁻¹) ?_
    (fun k b => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq k b).contDiffAt) i j
  intro a k
  refine contDiffAt_matrix_mul_entry
    (A := fun q' => l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹) ?_
    (fun k' b' => contDiffAt_l2A0Conjinv_entry_at H r B hB hr hL q hA0 k' b') a k
  intro a' k'
  exact contDiffAt_matrix_mul_entry
    (fun a'' k'' => (contDiff_l2Z1Conj_entry H r B hB hr hL a'' k'').contDiffAt)
    (fun k'' b'' => contDiffAt_l2A1Conjinv_entry_at H r B hB hr hL q hA1 k'' b'') a' k'

/-- `(Wc)⁻¹` entries `ContDiffAt` at `q` (`det A0c, A1c, Wc ≠ 0`). -/
theorem contDiffAt_l2WConjinv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0Conj H r B hB hr hL q).det ≠ 0) (hA1 : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => (l2WConj H r B hB hr hL hL2eq q')⁻¹ i j) q :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => contDiffAt_l2WConj_entry_at H r B hB hr hL hL2eq q hA0 hA1 a b) hW i j

/-- `S1c` entries `ContDiffAt` at `q` (`det A1c ≠ 0`). -/
theorem contDiffAt_l2S1Conj_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hA1 : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2S1Conj H r B hB hr hL hL2eq q' i j) q := by
  have heq : (fun q' => l2S1Conj H r B hB hr hL hL2eq q' i j)
      = fun q' => l2T1Conj H r hr hL q' i j
          - (l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹
              * l2Y1Conj H r B hB hr hL q') i j := by
    funext q'; rw [l2S1Conj, Matrix.sub_apply]
  rw [heq]
  refine (contDiff_l2T1Conj_entry H r hr hL i j).contDiffAt.sub ?_
  refine contDiffAt_matrix_mul_entry
    (A := fun q' => l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹) ?_
    (fun k b => (contDiff_l2Y1Conj_entry H r B hB hr hL k b).contDiffAt) i j
  intro a k
  exact contDiffAt_matrix_mul_entry
    (fun a' k' => (contDiff_l2Z1Conj_entry H r B hB hr hL a' k').contDiffAt)
    (fun k' b' => contDiffAt_l2A1Conjinv_entry_at H r B hB hr hL q hA1 k' b') a k

/-- `Brc` entries `ContDiffAt` at `q` (`det A0c, A1c, P00c ≠ 0`). -/
theorem contDiffAt_l2BrConj_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0Conj H r B hB hr hL q).det ≠ 0) (hA1 : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (hP00 : (l2P00Conj H r B hB hr hL hL2eq q).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2BrConj H r B hB hr hL hL2eq q' i j) q := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' : DeepestSplit H r (deepestNGauge H r) =>
        (((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2KConj H r B hB hr hL hL2eq q')
          * l2S1Conj H r B hB hr hL hL2eq q') i j) q := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
        (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2KConj H r B hB hr hL hL2eq q') ?_
      (fun k b => contDiffAt_l2S1Conj_entry_at H r B hB hr hL hL2eq q hA1 k b) i j
    intro a k
    have hsub : (fun q' => (1 - l2KConj H r B hB hr hL hL2eq q') a k)
        = fun q' => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) a k
            - l2KConj H r B hB hr hL hL2eq q' a k := by
      funext q'; rw [Matrix.sub_apply]
    rw [hsub]
    refine contDiffAt_const.sub ?_
    have hKeq : (fun q' => l2KConj H r B hB hr hL hL2eq q' a k)
        = fun q' => (l2Z1Conj H r B hB hr hL q' * (l2P00Conj H r B hB hr hL hL2eq q')⁻¹
            * l2Y0Conj H r B hB hr hL hL2eq q') a k := by
      funext q'; rw [l2KConj]
    rw [hKeq]
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => l2Z1Conj H r B hB hr hL q' * (l2P00Conj H r B hB hr hL hL2eq q')⁻¹) ?_
      (fun k' b' => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq k' b').contDiffAt) a k
    intro a' k'
    exact contDiffAt_matrix_mul_entry
      (fun a'' k'' => (contDiff_l2Z1Conj_entry H r B hB hr hL a'' k'').contDiffAt)
      (fun k'' b'' => contDiffAt_l2P00Conjinv_entry_at H r B hB hr hL hL2eq q hP00 k'' b'') a' k'
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' : DeepestSplit H r (deepestNGauge H r) =>
        (l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹
          * l2Y1Conj H r B hB hr hL q') i j) q := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹) ?_
      (fun k b => (contDiff_l2Y1Conj_entry H r B hB hr hL k b).contDiffAt) i j
    intro a k
    exact contDiffAt_matrix_mul_entry
      (fun a' k' => (contDiff_l2Z1Conj_entry H r B hB hr hL a' k').contDiffAt)
      (fun k' b' => contDiffAt_l2A1Conjinv_entry_at H r B hB hr hL q hA1 k' b') a k
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' : DeepestSplit H r (deepestNGauge H r) =>
        (l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹ * (l2A0Conj H r B hB hr hL q')⁻¹
          * l2Y0Conj H r B hB hr hL hL2eq q' * l2T1Conj H r hr hL q') i j) q := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹
          * (l2A0Conj H r B hB hr hL q')⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q') ?_
      (fun k b => (contDiff_l2T1Conj_entry H r hr hL k b).contDiffAt) i j
    intro a k
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹
          * (l2A0Conj H r B hB hr hL q')⁻¹) ?_
      (fun k' b' => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq k' b').contDiffAt) a k
    intro a' k'
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹) ?_
      (fun k'' b'' => contDiffAt_l2A0Conjinv_entry_at H r B hB hr hL q hA0 k'' b'') a' k'
    intro a'' k''
    exact contDiffAt_matrix_mul_entry
      (fun a3 k3 => (contDiff_l2Z1Conj_entry H r B hB hr hL a3 k3).contDiffAt)
      (fun k3 b3 => contDiffAt_l2A1Conjinv_entry_at H r B hB hr hL q hA1 k3 b3) a'' k''
  have heq : (fun q' => l2BrConj H r B hB hr hL hL2eq q' i j)
      = fun q' => (((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2KConj H r B hB hr hL hL2eq q')
          * l2S1Conj H r B hB hr hL hL2eq q') i j
          + (l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹
              * l2Y1Conj H r B hB hr hL q') i j
          + (l2Z1Conj H r B hB hr hL q' * (l2A1Conj H r B hB hr hL q')⁻¹ * (l2A0Conj H r B hB hr hL q')⁻¹
              * l2Y0Conj H r B hB hr hL hL2eq q' * l2T1Conj H r hr hL q') i j := by
    funext q'; rw [l2BrConj, Matrix.add_apply, Matrix.add_apply]
  rw [heq]
  exact (h1.add h2).add h3

/-- `T1'c` entries `ContDiffAt` at `q` (all four dets). -/
theorem contDiffAt_l2T1pConj_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0Conj H r B hB hr hL q).det ≠ 0) (hA1 : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (hP00 : (l2P00Conj H r B hB hr hL hL2eq q).det ≠ 0)
    (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2T1pConj H r B hB hr hL hL2eq q' i j) q := by
  have heq : (fun q' => l2T1pConj H r B hB hr hL hL2eq q' i j)
      = fun q' => ((l2WConj H r B hB hr hL hL2eq q')⁻¹ * l2BrConj H r B hB hr hL hL2eq q') i j := by
    funext q'; rw [l2T1pConj_eq]
  rw [heq]
  exact contDiffAt_matrix_mul_entry
    (fun a k => contDiffAt_l2WConjinv_entry_at H r B hB hr hL hL2eq q hA0 hA1 hW a k)
    (fun k b => contDiffAt_l2BrConj_entry_at H r B hB hr hL hL2eq q hA0 hA1 hP00 k b) i j

/-- `Y1'c` entries `ContDiffAt` at `q` (all four dets). -/
theorem contDiffAt_l2Y1pConj_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0Conj H r B hB hr hL q).det ≠ 0) (hA1 : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (hP00 : (l2P00Conj H r B hB hr hL hL2eq q).det ≠ 0)
    (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2Y1pConj H r B hB hr hL hL2eq q' i j) q := by
  have heq : (fun q' => l2Y1pConj H r B hB hr hL hL2eq q' i j)
      = fun q' => l2Y1Conj H r B hB hr hL q' i j
          + ((l2A0Conj H r B hB hr hL q')⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q'
              * (l2T1Conj H r hr hL q' - l2T1pConj H r B hB hr hL hL2eq q')) i j := by
    funext q'; rw [l2Y1pConj, Matrix.add_apply]
  rw [heq]
  refine (contDiff_l2Y1Conj_entry H r B hB hr hL i j).contDiffAt.add ?_
  refine contDiffAt_matrix_mul_entry
    (A := fun q' => (l2A0Conj H r B hB hr hL q')⁻¹ * l2Y0Conj H r B hB hr hL hL2eq q') ?_
    (fun k b => ?_) i j
  · intro a k
    exact contDiffAt_matrix_mul_entry
      (fun a' k' => contDiffAt_l2A0Conjinv_entry_at H r B hB hr hL q hA0 a' k')
      (fun k' b' => (contDiff_l2Y0Conj_entry H r B hB hr hL hL2eq k' b').contDiffAt) a k
  · have : (fun q' => (l2T1Conj H r hr hL q' - l2T1pConj H r B hB hr hL hL2eq q') k b)
        = fun q' => l2T1Conj H r hr hL q' k b - l2T1pConj H r B hB hr hL hL2eq q' k b := by
      funext q'; rw [Matrix.sub_apply]
    rw [this]
    exact (contDiff_l2T1Conj_entry H r hr hL k b).contDiffAt.sub
      (contDiffAt_l2T1pConj_entry_at H r B hB hr hL hL2eq q hA0 hA1 hP00 hW k b)

/-- The encoded conjugated core payload `ContDiffAt` at `q` (flat-codomain descent). -/
theorem contDiffAt_paramsEquivFlatCLE_l2CoreΔTupleConj_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0Conj H r B hB hr hL q).det ≠ 0) (hA1 : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (hP00 : (l2P00Conj H r B hB hr hL hL2eq q).det ≠ 0)
    (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q')) q := by
  refine contDiffAt_pi' (fun k => ?_)
  set d := (Fintype.equivFin (FlatIdx (deepestM H r))).symm k with hd
  have hcoord : (fun q' => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q') k)
      = fun q' => l2CoreΔTupleConj H r B hB hr hL hL2eq q' d.1.1 d.1.2 d.2 := by
    funext q'
    rw [show (⇑(paramsEquivFlatCLE (deepestM H r)) : Params (deepestM H r) → _)
        = ⇑(paramsEquivFlat (deepestM H r)) from paramsEquivFlatCLE_coe (deepestM H r)]
    rfl
  rw [hcoord]
  obtain ⟨⟨s, i⟩, j⟩ := d
  rcases eq_or_ne s (lastLayer hL) with hs | hs
  · subst hs
    have hentry : (fun q' => l2CoreΔTupleConj H r B hB hr hL hL2eq q' (lastLayer hL) i j)
        = fun q' => l2T1pConj H r B hB hr hL hL2eq q' i j - l2T1Conj H r hr hL q' i j := by
      funext q'; rw [l2CoreΔTupleConj, Function.update_self, Matrix.sub_apply]
    rw [hentry]
    exact (contDiffAt_l2T1pConj_entry_at H r B hB hr hL hL2eq q hA0 hA1 hP00 hW i j).sub
      (contDiff_l2T1Conj_entry H r hr hL i j).contDiffAt
  · have hentry : (fun q' => l2CoreΔTupleConj H r B hB hr hL hL2eq q' s i j) = fun _ => (0 : ℝ) := by
      funext q'; rw [l2CoreΔTupleConj, Function.update_of_ne hs]; rfl
    rw [hentry]; exact contDiffAt_const

/-- The conjugated gauge payload `ContDiffAt` at `q`. -/
theorem contDiffAt_l2GaugeΔConj_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0Conj H r B hB hr hL q).det ≠ 0) (hA1 : (l2A1Conj H r B hB hr hL q).det ≠ 0)
    (hP00 : (l2P00Conj H r B hB hr hL hL2eq q).det ≠ 0)
    (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (l2GaugeΔConj H r B hB hr hL hL2eq) q := by
  refine contDiffAt_pi' (fun idx => ?_)
  obtain ⟨s, rest⟩ := idx
  rcases rest with (rest | rest)
  · rcases rest with rest | ⟨i, j⟩
    · have h0 : (fun q' => l2GaugeΔConj H r B hB hr hL hL2eq q' ⟨s, Sum.inl (Sum.inl rest)⟩)
          = fun _ => (0 : ℝ) := by funext q'; simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply]; ring
      rw [h0]; exact contDiffAt_const
    · by_cases h : s = lastLayer hL
      · subst h
        -- payload = NEW read − OLD read = the delta `l2Y1pConj − l2Y1Conj` (deepest const cancels).
        have hY' : (fun q' => l2GaugeΔConj H r B hB hr hL hL2eq q'
              ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩)
            = fun q' => (l2Y1pConj H r B hB hr hL hL2eq q' - l2Y1Conj H r B hB hr hL q') i j := by
          funext q'
          have hg : regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2)
              ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩
              = readY H r hr hL (q'.1, q'.2.2) (lastLayer hL) i j := rfl
          simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply, dif_pos, hg]
          have := congrFun (congrFun (l2Y1pReadConj_sub_read_eq H r B hB hr hL hL2eq q') i) j
          rw [Matrix.sub_apply, Matrix.sub_apply] at this
          exact this
        rw [hY']
        exact (contDiffAt_l2Y1pConj_entry_at H r B hB hr hL hL2eq q hA0 hA1 hP00 hW i j).sub
          (contDiff_l2Y1Conj_entry H r B hB hr hL i j).contDiffAt
      · have h0 : (fun q' => l2GaugeΔConj H r B hB hr hL hL2eq q' ⟨s, Sum.inl (Sum.inr (i, j))⟩)
            = fun _ => (0 : ℝ) := by
          funext q'; simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply, dif_neg h]; ring
        rw [h0]; exact contDiffAt_const
  · have h0 : (fun q' => l2GaugeΔConj H r B hB hr hL hL2eq q' ⟨s, Sum.inr rest⟩) = fun _ => (0 : ℝ) := by
      funext q'; simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply]; ring
    rw [h0]; exact contDiffAt_const

/-! ## S2a — the conjugated joint unit set + cutoff bump

The cutoff χ support must sit where all four conjugated dets `A0c, A1c, P00c, Wc` are `≠ 0`. At the
origin those are `det(deepBlkA_0), det(deepBlkA_last), det(deepBlkA_0·deepBlkA_last), 1` — all `≠ 0`
given the pivot-base units `hDA0`/`hDA1` (and `hY` for `P00c(0)`). All four dets are continuous, so a
ball at `0` sits inside the joint unit set. -/

/-- The conjugated joint unit set: all four pivots/composites invertible. -/
def jointUnitSetConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    Set (DeepestSplit H r (deepestNGauge H r)) :=
  {q | (l2A0Conj H r B hB hr hL q).det ≠ 0 ∧ (l2A1Conj H r B hB hr hL q).det ≠ 0
    ∧ (l2P00Conj H r B hB hr hL hL2eq q).det ≠ 0 ∧ (l2WConj H r B hB hr hL hL2eq q).det ≠ 0}

/-- A ball at `0` inside the conjugated joint unit set (the four dets continuous, `≠ 0` at `0`). -/
theorem exists_ball_subset_jointUnitSetConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    ∃ ε > 0, Metric.ball (0 : DeepestSplit H r (deepestNGauge H r)) ε
      ⊆ jointUnitSetConj H r B hB hr hL hL2eq := by
  have hA0c : ContinuousAt (fun q => (l2A0Conj H r B hB hr hL q).det) 0 :=
    (contDiffAt_matrix_det_of_entries
      (fun a b => (contDiff_l2A0Conj_entry H r B hB hr hL a b).contDiffAt)).continuousAt
  have hA1c : ContinuousAt (fun q => (l2A1Conj H r B hB hr hL q).det) 0 :=
    (contDiffAt_matrix_det_of_entries
      (fun a b => (contDiff_l2A1Conj_entry H r B hB hr hL a b).contDiffAt)).continuousAt
  have hP00c : ContinuousAt (fun q => (l2P00Conj H r B hB hr hL hL2eq q).det) 0 := by
    refine (contDiffAt_matrix_det_of_entries (fun a b => ?_)).continuousAt
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
  have hWc : ContinuousAt (fun q => (l2WConj H r B hB hr hL hL2eq q).det) 0 := by
    refine (contDiffAt_matrix_det_of_entries (fun a b => ?_)).continuousAt
    exact contDiffAt_l2WConj_entry_at H r B hB hr hL hL2eq 0
      (l2A0Conj_det_ne_zero H r B hB hr hL hDA0) (l2A1Conj_det_ne_zero H r B hB hr hL hDA1) a b
  have hnbhd : jointUnitSetConj H r B hB hr hL hL2eq ∈ nhds (0 : DeepestSplit H r (deepestNGauge H r)) := by
    refine Filter.inter_mem (hA0c.preimage_mem_nhds (isOpen_ne.mem_nhds ?_))
      (Filter.inter_mem (hA1c.preimage_mem_nhds (isOpen_ne.mem_nhds ?_))
        (Filter.inter_mem (hP00c.preimage_mem_nhds (isOpen_ne.mem_nhds ?_))
          (hWc.preimage_mem_nhds (isOpen_ne.mem_nhds ?_))))
    · exact l2A0Conj_det_ne_zero H r B hB hr hL hDA0
    · exact l2A1Conj_det_ne_zero H r B hB hr hL hDA1
    · exact l2P00Conj_det_ne_zero H r B hB hr hL hL2eq hDA0 hDA1 hY
    · rw [l2WConj_zero H r B hB hr hL hL2eq (by
        -- need deepBlkZ_last = 0; supplied below via the boundary at last layer
        exact deepBlkZ_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL) (by
          simp only [lastLayer]; omega)), Matrix.det_one]
      exact one_ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnbhd
  exact ⟨ε, hε, hball⟩

/-- The chosen conjugated joint-unit radius. -/
noncomputable def jointRadiusConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) : ℝ :=
  (exists_ball_subset_jointUnitSetConj H r B hB hr hL hL2eq hDA0 hDA1 hY).choose

theorem jointRadiusConj_pos (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    0 < jointRadiusConj H r B hB hr hL hL2eq hDA0 hDA1 hY :=
  (exists_ball_subset_jointUnitSetConj H r B hB hr hL hL2eq hDA0 hDA1 hY).choose_spec.1

theorem ball_jointRadiusConj_subset (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    Metric.ball (0 : DeepestSplit H r (deepestNGauge H r))
        (jointRadiusConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
      ⊆ jointUnitSetConj H r B hB hr hL hL2eq :=
  (exists_ball_subset_jointUnitSetConj H r B hB hr hL hL2eq hDA0 hDA1 hY).choose_spec.2

/-- The conjugated cutoff bump (`jointRadiusConj/4`, `/2`), support in the joint unit set. -/
noncomputable def cutoffBumpSplitConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)) where
  rIn := jointRadiusConj H r B hB hr hL hL2eq hDA0 hDA1 hY / 4
  rOut := jointRadiusConj H r B hB hr hL hL2eq hDA0 hDA1 hY / 2
  rIn_pos := by have := jointRadiusConj_pos H r B hB hr hL hL2eq hDA0 hDA1 hY; linarith
  rIn_lt_rOut := by have := jointRadiusConj_pos H r B hB hr hL hL2eq hDA0 hDA1 hY; linarith

/-- The conjugated bump's tsupport sits in the joint unit set. -/
theorem tsupport_cutoffBumpSplitConj_subset (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    tsupport (fun q => ((cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY) q : ℝ))
      ⊆ jointUnitSetConj H r B hB hr hL hL2eq := by
  rw [(cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY).tsupport_eq]
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right] at hq
  have hpos := jointRadiusConj_pos H r B hB hr hL hL2eq hDA0 hDA1 hY
  have hrOut : (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY).rOut
      = jointRadiusConj H r B hB hr hL hL2eq hDA0 hDA1 hY / 2 := rfl
  rw [hrOut] at hq
  apply ball_jointRadiusConj_subset H r B hB hr hL hL2eq hDA0 hDA1 hY
  rw [Metric.mem_ball, dist_zero_right]; linarith

/-! ## S0/S1 — the public conjugated maps + S2/S3/S4

`psiSplitRawL2Conj := psiSplitRawL2CoreConj` (we only fire at `L = 2`). The cutoff `psiSplitCutL2Conj χ
q = q + χ q • (raw q − q)`, globally `ContDiff` (raw `ContDiffAt` on the joint-unit tsupport), fixes the
origin, has strict derivative `id` there (`D(raw − id)(0) = 0` + `δ(0) = 0`). `psiL2Conj` is the flat
conjugate `split⁻¹ ∘ psiSplitCutL2Conj ∘ split`. -/

/-- The conjugated raw joint correction `psiSplitRawL2CoreConj q − q`. -/
noncomputable def psiSplitDeltaL2Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q

/-- The conjugated χ-cutoff joint action `q + χ q • δc q`. -/
noncomputable def psiSplitCutL2Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  q + (χ q : ℝ) • psiSplitDeltaL2Conj H r B hB hr hL hL2eq q

/-- **The conjugated joint action fixes the split origin** (`psiSplitRawL2CoreConj 0 = 0`). Both lens
payloads vanish at the origin: the core payload `l2CoreΔTupleConj 0 = update 0 last 0 = 0`
(`l2T1pConj_sub_T1_zero`, `hZ`); the gauge payload `l2GaugeΔConj 0 = 0` (the new READ `l2Y1pReadConj 0
= 0` matches the old read `0`, all other tags are reads of `0`). -/
theorem psiSplitRawL2CoreConj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    psiSplitRawL2CoreConj H r B hB hr hL hL2eq (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
  have hsub : psiSplitRawL2CoreConj H r B hB hr hL hL2eq 0 - 0 = 0 := by
    rw [psiSplitDeltaL2CoreConj_eq_payload]
    have hcore0 : l2CoreΔTupleConj H r B hB hr hL hL2eq 0 = 0 := by
      rw [l2CoreΔTupleConj, l2T1pConj_sub_T1_zero H r B hB hr hL hL2eq hZ]
      exact Function.update_eq_self _ _
    have hgauge0 : l2GaugeΔConj H r B hB hr hL hL2eq 0 = 0 := by
      funext idx
      obtain ⟨s, rest⟩ := idx
      have hgz : regGaugeSlotEquiv H r hr hL ((0 : DeepestSplit H r (deepestNGauge H r)).1,
          (0 : DeepestSplit H r (deepestNGauge H r)).2.2) = 0 := by
        rw [gaugeProj_zero]; exact regGaugeSlotEquiv_zero H r hr hL
      rcases rest with (rest | rest)
      · rcases rest with rest | ⟨i, j⟩
        · simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply, hgz, Pi.zero_apply, sub_zero]
        · by_cases h : s = lastLayer hL
          · subst h
            -- the new read `l2Y1pReadConj 0 = 0`; the old read `regGaugeSlotEquiv 0 = 0`.
            have hRead0 : l2Y1pReadConj H r B hB hr hL hL2eq (0 : DeepestSplit H r (deepestNGauge H r))
                = 0 := l2Y1pReadConj_zero H r B hB hr hL hL2eq hY
            simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply, dif_pos, hgz, Pi.zero_apply, sub_zero]
            rw [hRead0]; rfl
          · simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply, dif_neg h, hgz, Pi.zero_apply, sub_zero]
      · simp only [l2GaugeΔConj, l2g'Conj, Pi.sub_apply, hgz, Pi.zero_apply, sub_zero]
    rw [hcore0, hgauge0]
    simp only [map_zero]
    rfl
  rwa [sub_zero] at hsub

/-- The conjugated correction vanishes at the split origin (`δc 0 = 0`). -/
theorem psiSplitDeltaL2Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    psiSplitDeltaL2Conj H r B hB hr hL hL2eq (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
  rw [psiSplitDeltaL2Conj, psiSplitRawL2CoreConj_zero H r B hB hr hL hL2eq hY hZ, sub_zero]

/-- The conjugated χ-cutoff joint action fixes the split origin (`χ • δc 0 = 0`). -/
theorem psiSplitCutL2Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r))) :
    psiSplitCutL2Conj H r B hB hr hL hL2eq χ (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
  simp only [psiSplitCutL2Conj, psiSplitDeltaL2Conj_zero H r B hB hr hL hL2eq hY hZ, smul_zero,
    add_zero]

/-! ## S2 — global ContDiff of the conjugated cutoff map (raw `ContDiffAt` on the joint-unit tsupport) -/

/-- The conjugated correction `δc = psiSplitRawL2CoreConj − id` is `ContDiffAt` on the bump's support
(the joint unit set, where all four conjugated dets `≠ 0`). -/
theorem contDiffAt_psiSplitDeltaL2Conj_of_mem_tsupport (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hq : q ∈ tsupport (fun y => ((cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY) y : ℝ))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (psiSplitDeltaL2Conj H r B hB hr hL hL2eq) q := by
  obtain ⟨hA0, hA1, hP00, hW⟩ := tsupport_cutoffBumpSplitConj_subset H r B hB hr hL hL2eq hDA0 hDA1 hY hq
  -- δc = encoded payloads (lens decomposition).
  have heq : psiSplitDeltaL2Conj H r B hB hr hL hL2eq
      = fun q' => (((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q')).1,
          (paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q'),
            ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q')).2)) := by
    funext q'; rw [psiSplitDeltaL2Conj]; exact psiSplitDeltaL2CoreConj_eq_payload H r B hB hr hL hL2eq q'
  rw [heq]
  have hrg : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' => (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔConj H r B hB hr hL hL2eq q')) q :=
    (regGaugeSlotCLE H r hr hL).symm.contDiff.contDiffAt.comp q
      (contDiffAt_l2GaugeΔConj_at H r B hB hr hL hL2eq q hA0 hA1 hP00 hW)
  have hcore : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTupleConj H r B hB hr hL hL2eq q')) q :=
    contDiffAt_paramsEquivFlatCLE_l2CoreΔTupleConj_at H r B hB hr hL hL2eq q hA0 hA1 hP00 hW
  exact (contDiffAt_fst.comp q hrg).prodMk ((hcore).prodMk (contDiffAt_snd.comp q hrg))

/-- **S2 — the conjugated cutoff map is globally `ContDiff ⊤`** (`q + χc • δc`, raw `ContDiffAt` on
`tsupport χc`, off-support the bump vanishes; `contDiff_contDiffBump_smul`). -/
theorem contDiff_psiSplitCutL2Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (psiSplitCutL2Conj H r B hB hr hL hL2eq (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)) := by
  have hcorr : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => ((cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY) q : ℝ)
        • psiSplitDeltaL2Conj H r B hB hr hL hL2eq q) :=
    contDiff_contDiffBump_smul (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
      (psiSplitDeltaL2Conj H r B hB hr hL hL2eq)
      (fun x hx => contDiffAt_psiSplitDeltaL2Conj_of_mem_tsupport H r B hB hr hL hL2eq hDA0 hDA1 hY x hx)
  have heq : psiSplitCutL2Conj H r B hB hr hL hL2eq (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
      = fun q => q + ((cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY) q : ℝ)
          • psiSplitDeltaL2Conj H r B hB hr hL hL2eq q := rfl
  rw [heq]
  exact contDiff_id.add hcorr

/-- **S4 — the conjugated cutoff map has strict derivative `id` at the split origin** (`D(δc)(0) = 0`
via the lens keystone + `δc(0) = 0`; the scalar–vector product rule). -/
theorem hasStrictFDerivAt_psiSplitCutL2Conj_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r))) :
    HasStrictFDerivAt (psiSplitCutL2Conj H r B hB hr hL hL2eq χ)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (0 : DeepestSplit H r (deepestNGauge H r)) := by
  have hχ : HasStrictFDerivAt (fun q => (χ q : ℝ))
      (fderiv ℝ (fun q => (χ q : ℝ)) 0) (0 : DeepestSplit H r (deepestNGauge H r)) :=
    (χ.contDiff (n := (1 : ℕ∞))).hasStrictFDerivAt (by norm_num)
  have hδ : HasStrictFDerivAt (psiSplitDeltaL2Conj H r B hB hr hL hL2eq)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0 := by
    have hk := hasStrictFDerivAt_psiSplitDeltaL2CoreConj_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ
    refine hk.congr_of_eventuallyEq ?_
    filter_upwards with q; rw [psiSplitDeltaL2Conj]
  have hδ0 : psiSplitDeltaL2Conj H r B hB hr hL hL2eq (0 : DeepestSplit H r (deepestNGauge H r)) = 0 :=
    psiSplitDeltaL2Conj_zero H r B hB hr hL hL2eq hY hZ
  have hsmul := hχ.smul hδ
  rw [hδ0] at hsmul
  simp only [smul_zero, ContinuousLinearMap.smulRight_zero, add_zero] at hsmul
  have hid : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) => q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 :=
    hasStrictFDerivAt_id 0
  have hsum := hid.add hsmul
  rw [add_zero] at hsum
  exact hsum.congr_of_eventuallyEq (by filter_upwards with q; rfl)

/-! ## S1 — the flat conjugate `psiL2Conj = split⁻¹ ∘ psiSplitCutL2Conj ∘ split` + S2/S3/S4 -/

/-- **The conjugated raw flat joint move** `split⁻¹ ∘ psiSplitRawL2CoreConj ∘ split` (the honest map,
no cutoff — used in the germ where `χc = 1`). -/
noncomputable def psiRawL2Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) :=
  fun w => (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).symm
    (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w))

/-- **The conjugated χ-cutoff flat joint move** `split⁻¹ ∘ psiSplitCutL2Conj χc ∘ split`. -/
noncomputable def psiL2Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) :=
  fun w => (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).symm
    (psiSplitCutL2Conj H r B hB hr hL hL2eq (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w))

/-- **S2 — `psiL2Conj` is `ContDiff ⊤`** (`split⁻¹ ∘ cutoff ∘ split`, all three `ContDiff`). -/
theorem psiL2Conj_contDiff (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (psiL2Conj H r B hB hr hL hL2eq hDA0 hDA1 hY) := by
  have heq : psiL2Conj H r B hB hr hL hL2eq hDA0 hDA1 hY
      = fun w => (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).symm
          (psiSplitCutL2Conj H r B hB hr hL hL2eq (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
            (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w)) := rfl
  rw [heq]
  exact (contDiff_deepestSplit_symm H r hr hL (wstarL2 H r B hB hr hL)).comp
    ((contDiff_psiSplitCutL2Conj H r B hB hr hL hL2eq hDA0 hDA1 hY).comp
      (contDiff_deepestSplit H r hr hL (wstarL2 H r B hB hr hL)))

/-- **S3 — fixpoint** `psiL2Conj wstar = wstar` (`split wstar = 0`, `χc • δc 0 = 0`). -/
theorem psiL2Conj_fixpoint (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    psiL2Conj H r B hB hr hL hL2eq hDA0 hDA1 hY wstar = wstar := by
  have hwstar' : wstarL2 H r B hB hr hL = wstar := by rw [wstarL2, hwstar]
  have hbase : deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar = 0 := by
    rw [hwstar']; exact (deepestSplit_mp_basepoint H r hr hL wstar).2
  simp only [psiL2Conj, hbase, psiSplitCutL2Conj_zero H r B hB hr hL hL2eq hY hZ]
  rw [← hbase, (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).symm_apply_apply]

/-- **S4 — `psiL2Conj` has strict derivative `id` at `wstar`** (chain rule: `split` CLE at `wstar`,
`id` at the origin via `hasStrictFDerivAt_psiSplitCutL2Conj_zero`, `split⁻¹` CLE; `e = refl`). -/
theorem psiL2Conj_hasStrictFDerivAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    HasStrictFDerivAt (psiL2Conj H r B hB hr hL hL2eq hDA0 hDA1 hY)
      (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) wstar := by
  have hwstar' : wstarL2 H r B hB hr hL = wstar := by rw [wstarL2, hwstar]
  have hbase : deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar = 0 := by
    rw [hwstar']; exact (deepestSplit_mp_basepoint H r hr hL wstar).2
  have hsplit := hasStrictFDerivAt_deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar
  have hcut0 := hasStrictFDerivAt_psiSplitCutL2Conj_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ
    (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
  have hcut : HasStrictFDerivAt
      (psiSplitCutL2Conj H r B hB hr hL hL2eq (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY))
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar) := by rw [hbase]; exact hcut0
  have hsymm := hasStrictFDerivAt_deepestSplit_symm H r hr hL (wstarL2 H r B hB hr hL)
    (psiSplitCutL2Conj H r B hB hr hL hL2eq (cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar))
  have hcomp := (hsymm.comp wstar (hcut.comp wstar hsplit))
  refine hcomp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact (deepestSplitCLE H r hr hL).symm_apply_apply w

/-- **Near `wstar` the conjugated cutoff move equals the honest raw move** (`χc = 1` germ). -/
theorem psiL2Conj_eventuallyEq_psiRawL2Conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    psiL2Conj H r B hB hr hL hL2eq hDA0 hDA1 hY
      =ᶠ[nhds wstar] psiRawL2Conj H r B hB hr hL hL2eq := by
  have hwstar' : wstarL2 H r B hB hr hL = wstar := by rw [wstarL2, hwstar]
  have hbase : deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar = 0 := by
    rw [hwstar']; exact (deepestSplit_mp_basepoint H r hr hL wstar).2
  have hχ1 : (fun w => ((cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w) : ℝ)) =ᶠ[nhds wstar] 1 := by
    have hcont : ContinuousAt (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)) wstar :=
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).continuous.continuousAt
    have htend : Filter.Tendsto (deepestSplit H r hr hL (wstarL2 H r B hB hr hL))
        (nhds wstar) (nhds 0) := by rw [← hbase]; exact hcont
    exact htend.eventually ((cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY).eventuallyEq_one)
  filter_upwards [hχ1] with w hw
  simp only [psiL2Conj, psiRawL2Conj, psiSplitCutL2Conj, psiSplitDeltaL2Conj]
  have hw' : ((cutoffBumpSplitConj H r B hB hr hL hL2eq hDA0 hDA1 hY)
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w) : ℝ) = 1 := hw
  rw [hw', one_smul, add_sub_cancel]

/-- `split ∘ psiRawL2Conj = psiSplitRawL2CoreConj ∘ split` (the conjugate's split-conjugacy `rfl`). -/
theorem psiRawL2Conj_split (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (x : Fin (flatDim H) → ℝ) :
    deepestSplit H r hr hL (wstarL2 H r B hB hr hL) (psiRawL2Conj H r B hB hr hL hL2eq x)
      = psiSplitRawL2CoreConj H r B hB hr hL hL2eq
          (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) x) := by
  rw [psiRawL2Conj, (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).apply_symm_apply]

/-! ## S6r — the conjugated read-fixing lemmas (the move fixes layer-0 + X/Z reads)

`l2g'Conj` edits ONLY the last-layer `Y`-tag (writing `l2Y1pReadConj`), so every other read is fixed.
These are the conjugated analogues of `readX/Y/Z_psiSplitRawL2Core_eq` (the move's read-transport). -/

/-- The moved gauge slot `((ψq).1, (ψq).2.2) = regGaugeSlotEquiv.symm (l2g'Conj q)`. -/
theorem psiSplitRawL2CoreConj_gauge (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2)
      = (regGaugeSlotEquiv H r hr hL).symm (l2g'Conj H r B hB hr hL hL2eq q) := by
  rw [psiSplitRawL2CoreConj_eq]

/-- `readX(ψq) = readX(q)` (X-tags untouched). -/
theorem readX_psiSplitRawL2CoreConj_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    readX H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) s
      = readX H r hr hL (q.1, q.2.2) s := by
  ext i j
  rw [psiSplitRawL2CoreConj_gauge, readX_regGaugeSlotEquiv_symm]; rfl

/-- `readZ(ψq) = readZ(q)` (Z-tags untouched). -/
theorem readZ_psiSplitRawL2CoreConj_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    readZ H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) s
      = readZ H r hr hL (q.1, q.2.2) s := by
  ext i j
  rw [psiSplitRawL2CoreConj_gauge, readZ_regGaugeSlotEquiv_symm]; rfl

/-- `readY(ψq) = readY(q)` at a NON-last layer (`else` branch of `l2g'Conj`). -/
theorem readY_psiSplitRawL2CoreConj_of_ne_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL) :
    readY H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) s
      = readY H r hr hL (q.1, q.2.2) s := by
  ext i j
  rw [psiSplitRawL2CoreConj_gauge, readY_regGaugeSlotEquiv_symm]
  show l2g'Conj H r B hB hr hL hL2eq q ⟨s, Sum.inl (Sum.inr (i, j))⟩
      = readY H r hr hL (q.1, q.2.2) s i j
  rw [l2g'Conj]; simp only [dif_neg hs]; rfl

/-- `readY(ψq)_last = l2Y1pReadConj` (the moved last-Y read). -/
theorem readY_psiSplitRawL2CoreConj_last_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    readY H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) (lastLayer hL)
      = l2Y1pReadConj H r B hB hr hL hL2eq q := by
  ext i j
  rw [psiSplitRawL2CoreConj_gauge, readY_regGaugeSlotEquiv_symm]
  show l2g'Conj H r B hB hr hL hL2eq q ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩
      = l2Y1pReadConj H r B hB hr hL hL2eq q i j
  rw [l2g'Conj]; simp only [dif_pos rfl]; rfl

/-- `coreRead(ψq)_s = coreRead(q)_s` at a NON-last layer (core update only at `last`). -/
theorem coreRead_psiSplitRawL2CoreConj_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.1 s
      = (paramsEquivFlat (deepestM H r)).symm q.2.1 s := by
  have hcore : (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.1
      = paramsEquivFlat (deepestM H r)
          (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1)
            (lastLayer hL) (l2T1pConj H r B hB hr hL hL2eq q)) := by
    rw [psiSplitRawL2CoreConj_eq]
  rw [hcore, coreDecode_paramsEquivFlat, Function.update_of_ne hs]

/-- `coreRead(ψq)_last = l2T1pConj` (the moved core block, written literally). -/
theorem coreRead_psiSplitRawL2CoreConj_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.1
        (lastLayer hL)
      = l2T1pConj H r B hB hr hL hL2eq q := by
  have hcore : (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.1
      = paramsEquivFlat (deepestM H r)
          (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1)
            (lastLayer hL) (l2T1pConj H r B hB hr hL hL2eq q)) := by
    rw [psiSplitRawL2CoreConj_eq]
  rw [hcore, coreDecode_paramsEquivFlat, Function.update_self]

/-! ## S6c — the conjugated absorbed per-layer cores of the moved point

The conjugated absorbed core `decode(ψq).core_s + schurCorrectionConj(ψq)_s`. At the last layer the
deepest blocks combine with the moved reads: the conjugated `Y1c(ψq) = deepBlkY_last + readY_last(ψq) =
deepBlkY_last + l2Y1pReadConj = l2Y1pConj` (= `Y1'c`), so `c_last = T1'c − Z1c·A1c⁻¹·Y1'c = (1−Kc)·S1c`
(the conjugated keystone). Off the last layer everything is fixed. -/

/-- The conjugated keystone `T1'c − Z1c·A1c⁻¹·Y1'c = (1−Kc)·S1c` (`det Wc ≠ 0`). Pure algebra over the
`l2*Conj` defs, mirroring `l2T1p_sub_Z1A1invY1p_eq`. -/
theorem l2T1pConj_sub_Z1A1invY1pConj_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0) :
    l2T1pConj H r B hB hr hL hL2eq q
        - l2Z1Conj H r B hB hr hL q * (l2A1Conj H r B hB hr hL q)⁻¹ * l2Y1pConj H r B hB hr hL hL2eq q
      = (1 - l2KConj H r B hB hr hL hL2eq q) * l2S1Conj H r B hB hr hL hL2eq q := by
  set Z1 := l2Z1Conj H r B hB hr hL q with hZ1
  set A1i := (l2A1Conj H r B hB hr hL q)⁻¹ with hA1i
  set A0i := (l2A0Conj H r B hB hr hL q)⁻¹ with hA0i
  set Y0 := l2Y0Conj H r B hB hr hL hL2eq q with hY0
  set Y1 := l2Y1Conj H r B hB hr hL q with hY1
  set T1 := l2T1Conj H r hr hL q with hT1
  set T1' := l2T1pConj H r B hB hr hL hL2eq q with hT1'
  set K := l2KConj H r B hB hr hL hL2eq q with hK
  set S1 := l2S1Conj H r B hB hr hL hL2eq q with hS1
  have hRdef : l2RConj H r B hB hr hL hL2eq q = Z1 * A1i * A0i * Y0 := rfl
  have hY1p : l2Y1pConj H r B hB hr hL hL2eq q = Y1 + A0i * Y0 * (T1 - T1') := rfl
  have hZAY1p : Z1 * A1i * l2Y1pConj H r B hB hr hL hL2eq q
      = Z1 * A1i * Y1 + l2RConj H r B hB hr hL hL2eq q * (T1 - T1') := by
    rw [hY1p, Matrix.mul_add, hRdef]; simp only [Matrix.mul_assoc]
  have hWWi : l2WConj H r B hB hr hL hL2eq q * (l2WConj H r B hB hr hL hL2eq q)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Ne.isUnit hW)
  have hWT1' : l2WConj H r B hB hr hL hL2eq q * T1' = l2BrConj H r B hB hr hL hL2eq q := by
    rw [hT1', l2T1pConj_eq, ← Matrix.mul_assoc, hWWi, Matrix.one_mul]
  rw [hZAY1p, hRdef] at *
  have hWdef : l2WConj H r B hB hr hL hL2eq q = 1 + Z1 * A1i * A0i * Y0 := rfl
  have key : T1' - (Z1 * A1i * Y1 + Z1 * A1i * A0i * Y0 * (T1 - T1'))
      = l2BrConj H r B hB hr hL hL2eq q - Z1 * A1i * Y1 - Z1 * A1i * A0i * Y0 * T1 := by
    rw [← hWT1', hWdef, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub]; abel
  rw [key, l2BrConj]
  rw [Matrix.mul_assoc (Z1 * A1i * A0i) Y0 T1]
  abel

/-- The conjugated moved last-layer Schur correction `schurCorrectionConj(ψq)_last = −Z1c·A1c⁻¹·Y1'c`.
At the last layer `readZ(ψq) = readZ(q)`, `readX(ψq) = readX(q)` (so `A0c/A1c/Z1c` fixed), and `readY(ψq)
= l2Y1pReadConj`, so the conjugated `Y1c(ψq) = deepBlkY_last + l2Y1pReadConj = l2Y1pConj = Y1'c`. -/
theorem schurCorrectionConj_psiSplitRawL2CoreConj_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    schurCorrectionConj H r B hB hr hL
        ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2)
        (lastLayer hL)
      = -(l2Z1Conj H r B hB hr hL q) * (l2A1Conj H r B hB hr hL q)⁻¹
          * l2Y1pConj H r B hB hr hL hL2eq q := by
  rw [schurCorrectionConj]
  -- deepBlkZ_last + readZ(ψq)_last = l2Z1Conj q; deepBlkA_last + readX(ψq)_last = l2A1Conj q;
  -- deepBlkY_last + readY(ψq)_last = deepBlkY_last + l2Y1pReadConj = l2Y1pConj.
  rw [readZ_psiSplitRawL2CoreConj_eq, readX_psiSplitRawL2CoreConj_eq,
    readY_psiSplitRawL2CoreConj_last_eq]
  have hZ1 : deepBlkZ H r B hB hr hL (lastLayer hL) + readZ H r hr hL (q.1, q.2.2) (lastLayer hL)
      = l2Z1Conj H r B hB hr hL q := rfl
  have hA1 : deepBlkA H r B hB hr hL (lastLayer hL) + readX H r hr hL (q.1, q.2.2) (lastLayer hL)
      = l2A1Conj H r B hB hr hL q := rfl
  have hY1 : deepBlkY H r B hB hr hL (lastLayer hL) + l2Y1pReadConj H r B hB hr hL hL2eq q
      = l2Y1pConj H r B hB hr hL hL2eq q := by
    rw [l2Y1pReadConj, l2Y1pConj, l2Y1Conj]; abel
  rw [hZ1, hA1, hY1, Matrix.neg_mul, Matrix.neg_mul]

/-- **The conjugated absorbed last-layer core IS `(1−Kc)·S1c`** (`det Wc ≠ 0`). -/
theorem absorbedCoreConj_psiSplitRawL2CoreConj_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.1
        (lastLayer hL)
        + schurCorrectionConj H r B hB hr hL
            ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
              (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2)
            (lastLayer hL)
      = (1 - l2KConj H r B hB hr hL hL2eq q) * l2S1Conj H r B hB hr hL hL2eq q := by
  rw [coreRead_psiSplitRawL2CoreConj_last, schurCorrectionConj_psiSplitRawL2CoreConj_last,
    ← l2T1pConj_sub_Z1A1invY1pConj_eq H r B hB hr hL hL2eq q hW, sub_eq_add_neg]
  congr 1
  rw [Matrix.neg_mul, Matrix.neg_mul]

/-- **The conjugated absorbed cores agree off the last layer** (reads + decode-core fixed). -/
theorem absorbedCoreConj_psiSplitRawL2CoreConj_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.1 s
        + schurCorrectionConj H r B hB hr hL
            ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
              (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) s
      = (paramsEquivFlat (deepestM H r)).symm q.2.1 s
        + schurCorrectionConj H r B hB hr hL (q.1, q.2.2) s := by
  rw [coreRead_psiSplitRawL2CoreConj_of_ne H r B hB hr hL hL2eq q s hs]
  congr 1
  rw [schurCorrectionConj, schurCorrectionConj, readZ_psiSplitRawL2CoreConj_eq,
    readX_psiSplitRawL2CoreConj_eq, readY_psiSplitRawL2CoreConj_of_ne_eq H r B hB hr hL hL2eq q s hs]

/-- **The conjugated absorbed-core tuple cleans to `C`** (the `hc_eq` step): the per-layer absorbed core
`decode(ψq).core_s + schurCorrectionConj(ψq)_s` equals the cleaned tuple `update (decode q + corrConj q)
last ((1−Kc)·S1c)` — last via `absorbedCoreConj_psiSplitRawL2CoreConj_last` (`det Wc ≠ 0`), off-last via
`_of_ne`. The conjugated analogue of the bare `hc_eq`. -/
theorem absorbedCoreConj_psiSplitRawL2CoreConj_eq_clean (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0) :
    (fun s => (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.1 s
        + schurCorrectionConj H r B hB hr hL
            ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
              (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) s)
      = Function.update
          (fun s => (paramsEquivFlat (deepestM H r)).symm q.2.1 s
            + schurCorrectionConj H r B hB hr hL (q.1, q.2.2) s)
          (lastLayer hL)
          ((1 - l2KConj H r B hB hr hL hL2eq q) * l2S1Conj H r B hB hr hL hL2eq q) := by
  funext s
  by_cases hs : s = lastLayer hL
  · subst hs
    rw [Function.update_self]
    exact absorbedCoreConj_psiSplitRawL2CoreConj_last H r B hB hr hL hL2eq q hW
  · rw [Function.update_of_ne hs]
    exact absorbedCoreConj_psiSplitRawL2CoreConj_of_ne H r B hB hr hL hL2eq q s hs

/-- **Step Ψ_conj sub-4 (in-file, modulo the conjugated LDU readback-tie).** On the inner ball, the
conjugated absorbed-core energy of the moved point equals the Score: by stage-5
`deepestCoreF_coreAbsorbConj_eq_prodSchur` + the tuple-clean (above) + the conjugated readback-tie
`hLDUtieConj` (`prod(deepestM) C = Score integrand`, TRUE here — discharged via
`prod_deepestM_eq_schur_ldu_readback` + `absorbedCoreConj_eq_schurCore` after the `Fin 3` subst at the
wire/below). The conjugated analogue of the bare `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score`, with
the now-TRUE conjugated dictionary in place of the bare-false one. -/
theorem deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (q : DeepestSplit H r (deepestNGauge H r))
    (hq : psiSplitRawL2CoreConj H r B hB hr hL hL2eq q
      ∈ Metric.closedBall (0 : DeepestSplit H r (deepestNGauge H r))
        ((cutoffBumpConj H r B hB hr hL hDA).rIn))
    (hW : (l2WConj H r B hB hr hL hL2eq q).det ≠ 0)
    (Score : ℝ)
    (hLDUtieConj : frobSq (prod (deepestM H r)
        (Function.update
          (fun s => (paramsEquivFlat (deepestM H r)).symm q.2.1 s
            + schurCorrectionConj H r B hB hr hL (q.1, q.2.2) s)
          (lastLayer hL)
          ((1 - l2KConj H r B hB hr hL hL2eq q) * l2S1Conj H r B hB hr hL hL2eq q))) = Score) :
    deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q)).2.1 = Score := by
  rw [deepestCoreF_coreAbsorbConj_eq_prodSchur H r B hB hr hL hDA
    (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q) hq,
    absorbedCoreConj_psiSplitRawL2CoreConj_eq_clean H r B hB hr hL hL2eq q hW, hLDUtieConj]

/-- **`framedParamsPivot` of the moved point agrees off the last layer** (the `hsub3reg` reg-input the
wire consumes): at a non-last layer the conjugated move fixes every read + the decode-core, so the
framed layer is unchanged. Conjugated mirror of `framedParamsPivot_psiSplitRawL2Core_of_ne`. -/
theorem framedParamsPivot_psiSplitRawL2CoreConj_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL) :
    framedParamsPivot H r hr hL J P Q (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q) s
      = framedParamsPivot H r hr hL J P Q q s := by
  rw [framedParamsPivot_of_ne_last H r hr hL J P Q (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q) s hs,
    framedParamsPivot_of_ne_last H r hr hL J P Q q s hs]
  show framedLayer H r hr s (P s) (Q s)
      (readX H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) s)
      (readY H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) s)
      (readZ H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.2) s)
      ((paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q).2.1 s)
    = framedLayer H r hr s (P s) (Q s)
      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
      (readZ H r hr hL (q.1, q.2.2) s) ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)
  rw [readX_psiSplitRawL2CoreConj_eq, readZ_psiSplitRawL2CoreConj_eq,
    readY_psiSplitRawL2CoreConj_of_ne_eq H r B hB hr hL hL2eq q s hs,
    coreRead_psiSplitRawL2CoreConj_of_ne H r B hB hr hL hL2eq q s hs]

/-! ## S6t — the chart-point block-read identities (`l2*Conj(split x) = reindex(decode x) blocks`)

At the deepest-split chart point `q = deepestSplit w0 x`, the conjugated named blocks ARE the reindexed
decode-`x` layer blocks: `l2A·Conj = .toBlocks₁₁`, off-diagonals `= .toBlocks₁₂/₂₁`, `l2T1Conj =
.toBlocks₂₂` (deepBlkT_last = 0). These convert the readback's reindexed-decode-`x` Schur shapes
(`hC0`/`hC1`) to the apparatus `l2KConj`/`l2S1Conj`. Derived from `reindex_decode_blocks_split`. -/

/-- The reindexed decode-`x` layer-`s` block decomposition at the split point: `reindex(decode x)_s =
reindex(deepest)_s + fromBlocks (readX/Y/Z, core)(split x)_s` — the four blocks read as `deepBlk· +
read·` (`toBlocks₁₁/₁₂/₂₁`) and `core` (`toBlocks₂₂`, `deepBlk_s.toBlocks₂₂ = 0` at boundary). -/
theorem reindex_decode_split_blocks (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (x : Fin (flatDim H) → ℝ) (s : Fin L) :
    Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
          (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)
        + Matrix.fromBlocks
            (readX H r hr hL ((deepestSplit H r hr hL ((paramsEquivFlat H)
              (deepestPoint H r B hB hr hL)) x).1,
              (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x).2.2) s)
            (readY H r hr hL ((deepestSplit H r hr hL ((paramsEquivFlat H)
              (deepestPoint H r B hB hr hL)) x).1,
              (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x).2.2) s)
            (readZ H r hr hL ((deepestSplit H r hr hL ((paramsEquivFlat H)
              (deepestPoint H r B hB hr hL)) x).1,
              (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x).2.2) s)
            ((paramsEquivFlat (deepestM H r)).symm
              (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x).2.1 s) :=
  reindex_decode_blocks_split H r B hB hr hL x s

/-- At a layer where `deepBlk_s.toBlocks₂₂ = 0` (boundary `hT`), the reindexed decode-`x` block reads,
at the split point `q = deepestSplit w0 x`: `₁₁ = deepBlkA_s + readX(q)_s`, `₂₁ = deepBlkZ_s + readZ(q)_s`,
`₁₂ = deepBlkY_s + readY(q)_s`, `₂₂ = decode(q).core_s`. Mirrors `absorbedCoreConj_eq_schurCore`'s body. -/
theorem reindex_decode_split_toBlocks (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (x : Fin (flatDim H) → ℝ) (s : Fin L)
    (hT : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0) :
    let q := deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x
    let MX := Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)
    MX.toBlocks₁₁ = deepBlkA H r B hB hr hL s + readX H r hr hL (q.1, q.2.2) s
      ∧ MX.toBlocks₂₁ = deepBlkZ H r B hB hr hL s + readZ H r hr hL (q.1, q.2.2) s
      ∧ MX.toBlocks₁₂ = deepBlkY H r B hB hr hL s + readY H r hr hL (q.1, q.2.2) s
      ∧ MX.toBlocks₂₂ = (paramsEquivFlat (deepestM H r)).symm q.2.1 s := by
  intro q MX
  set MD := Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
      (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s) with hMD
  set FB := Matrix.fromBlocks (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
      (readZ H r hr hL (q.1, q.2.2) s) ((paramsEquivFlat (deepestM H r)).symm q.2.1 s) with hFB
  have hsplit : MX = MD + FB := reindex_decode_split_blocks H r B hB hr hL x s
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i j
    rw [hsplit]
    show MD (Sum.inl i) (Sum.inl j) + FB (Sum.inl i) (Sum.inl j) = _
    rw [hFB, Matrix.fromBlocks_apply₁₁]; rfl
  · funext i j
    rw [hsplit]
    show MD (Sum.inr i) (Sum.inl j) + FB (Sum.inr i) (Sum.inl j) = _
    rw [hFB, Matrix.fromBlocks_apply₂₁]; rfl
  · funext i j
    rw [hsplit]
    show MD (Sum.inl i) (Sum.inr j) + FB (Sum.inl i) (Sum.inr j) = _
    rw [hFB, Matrix.fromBlocks_apply₁₂]; rfl
  · funext i j
    rw [hsplit]
    have hMD22 : MD.toBlocks₂₂ i j = 0 := by rw [hMD] at hT ⊢; rw [hT]; rfl
    show MD (Sum.inr i) (Sum.inr j) + FB (Sum.inr i) (Sum.inr j) = _
    have : MD (Sum.inr i) (Sum.inr j) = 0 := hMD22
    rw [this, zero_add, hFB, Matrix.fromBlocks_apply₂₂]

/-! ## S6t — the conjugated LDU readback-tie `hLDUtieConj` (Steps B-E)

The standalone discharge of the readback-tie `frobSq (prod (deepestM) C) = Score x`, where `C` is the
cleaned conjugated tuple `update (decode q + corrConj q) last ((1−Kc)·S1c)` at `q = deepestSplit w0 x`.
Via the banked `prod_deepestM_eq_schur_ldu_readback` (`Fin 3`): the cleaned tuple's `hC0`/`hC1` read
exactly the reindexed-decode-`x` Schur shapes the readback consumes (Step C, from the block-reads Step A
+ the `P00c = Mid₁₁` Step B), then `subst hL2eq` LATE applies the readback (Step E). -/

/-- **Step B — `P00c = Mid₁₁`.** The conjugated full-product `(1,1)` block equals the reindexed product's
`(1,1)` block: `l2P00Conj (split x) = (reindex(prod x)).toBlocks₁₁`. -/
theorem l2P00Conj_eq_reindex_prod_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (x : Fin (flatDim H) → ℝ)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr) :
    l2P00Conj H r B hB hr hL hL2eq
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x)
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁ := by
  subst hL2eq
  -- `J = frontEmbed` ⟹ the column pivot split IS the threshold split.
  rw [hJfront, pivotThresholdSplit_frontEmbed]
  set q := deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x with hq
  -- The two decode layers (bare matrices); `L1`'s codomain typed at `H (Fin.last 2)` to match the goal.
  set L0 : Matrix (Fin (H 0)) (Fin (H 1)) ℝ := ((paramsEquivFlat H).symm x) (0 : Fin 2) with hL0
  set L1 : Matrix (Fin (H 1)) (Fin (H (Fin.last 2))) ℝ := ((paramsEquivFlat H).symm x) (1 : Fin 2)
    with hL1
  have hMidfac : prod H ((paramsEquivFlat H).symm x) = L0 * L1 := by
    rw [prodDecode_eq_two_of_L2 H ((paramsEquivFlat H).symm x)]
    simp only [finCongr_refl, Matrix.reindex_refl_refl]
    rfl
  rw [hMidfac, reindex_mul_fromBlocks (rThresholdSplit r (H 0) (hr 0))
    (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2))) L0 L1,
    Matrix.toBlocks_fromBlocks₁₁]
  -- Step A block reads at the two layers (`s = ⟨0⟩` and `s = lastLayer`).
  have hT0 := deepBlkT_layer0_zero H r B hB hr hL (by omega) (⟨0, by omega⟩ : Fin 2) (by rfl)
  have hT1 := deepBlkT_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL) (by rfl)
  obtain ⟨hA0, hZ0, hY0, _⟩ := reindex_decode_split_toBlocks H r B hB hr hL x (⟨0, by omega⟩ : Fin 2) hT0
  obtain ⟨hA1, hZ1, _hY1, _⟩ := reindex_decode_split_toBlocks H r B hB hr hL x (lastLayer hL) hT1
  rw [l2P00Conj, l2A0Conj, l2A1Conj, l2Z1Conj, l2Y0Conj]
  rw [← hA0, ← hA1, ← hZ1]
  congr 1
  rw [← hY0]
  rw [show finCongr (midWidth_eq_of_L2 H r hL rfl) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl]
  rfl

/-- **The cleaned conjugated tuple `C`** at `q = deepestSplit w0 x`: the per-layer absorbed core, with the
last layer set to `(1−Kc)·S1c`. (= the `C` the bridge's `hLDUtieConj` reads.) -/
noncomputable def hLDUtieConjC (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (x : Fin (flatDim H) → ℝ) : Params (deepestM H r) :=
  Function.update
    (fun s => (paramsEquivFlat (deepestM H r)).symm
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x).2.1 s
      + schurCorrectionConj H r B hB hr hL
          ((deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x).1,
            (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x).2.2) s)
    (lastLayer hL)
    ((1 - l2KConj H r B hB hr hL hL2eq
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x))
      * l2S1Conj H r B hB hr hL hL2eq
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x))

/-- **Steps B-E — the conjugated LDU readback-tie.** `frobSq (prod (deepestM) C) = frobSq (Score-Schur)`
at the chart point, via `prod_deepestM_eq_schur_ldu_readback`. The `hC0`/`hC1` the readback needs read the
reindexed decode-`x` Schur shapes; `C`'s last layer is `(1−Kc)·S1c` (matched via Step B/C). -/
theorem frobSq_prod_deepestM_hLDUtieConjC_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hP22 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₂₂ = 1)
    (hQ22 : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₂ = 1)
    (x : Fin (flatDim H) → ℝ)
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁)
    (hQ11inv : Invertible (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (endpointQL H hL Qf)).toBlocks₁₁)
    (hMid11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁)
    (hA0inv : Invertible (Matrix.reindex
          (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).castSucc) (hr (⟨0, by omega⟩ : Fin L).castSucc))
          (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).succ) (hr (⟨0, by omega⟩ : Fin L).succ))
        (((paramsEquivFlat H).symm x) (⟨0, by omega⟩ : Fin L))).toBlocks₁₁)
    (hA1inv : Invertible (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc)
          (hr (lastLayer hL).castSucc)) (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₁₁) :
    frobSq (prod (deepestM H r) (hLDUtieConjC H r B hB hr hL hL2eq x))
      = frobSq ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
              * endpointQL H hL Qf)).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                * endpointQL H hL Qf)).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₂) := by
  -- It suffices to identify `prod (deepestM) C` with the Score-Schur matrix, then `congrArg frobSq`.
  refine congrArg frobSq ?_
  -- Step E: subst LATE — but at the spine, so the Fin-3 readback + its `Fin 2` block reads typecheck.
  subst hL2eq
  -- Step B: `P00c = Mid₁₁`.
  have hP00 := l2P00Conj_eq_reindex_prod_toBlocks₁₁ H r B hB hr hL rfl x J hJfront
  set q := deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x with hq
  -- The cleaned-tuple readback conditions `hC0`/`hC1`.
  have hC0 : Matrix.reindex (finCongr (rfl : deepestM H r 0 = deepestM H r ((0 : Fin 2)).castSucc))
        (finCongr (rfl : deepestM H r 1 = deepestM H r ((0 : Fin 2)).succ))
        (hLDUtieConjC H r B hB hr hL rfl x (0 : Fin 2))
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
            (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
              (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂ := by
    -- Collapse the trivial `finCongr` reindexes.
    rw [finCongr_refl, finCongr_refl]
    erw [Matrix.reindex_refl_refl]
    -- `C 0 = decode(q).core_0 + corrConj(q)_0` (`0 ≠ lastLayer`).
    rw [hLDUtieConjC,
      Function.update_of_ne (show (0 : Fin 2) ≠ lastLayer hL from
        Fin.ne_of_val_ne (by simp [lastLayer]))]
    -- The schur-core keystone at layer 0 (`hT = deepBlkT_layer0_zero`).
    exact absorbedCoreConj_eq_schurCore H r B hB hr hL x (⟨0, by omega⟩ : Fin 2)
      (deepBlkT_layer0_zero H r B hB hr hL (by omega) (⟨0, by omega⟩ : Fin 2) (by rfl))
  have hC1 : Matrix.reindex (finCongr (rfl : deepestM H r 1 = deepestM H r ((1 : Fin 2)).castSucc))
        (finCongr (rfl : deepestM H r (Fin.last 2) = deepestM H r ((1 : Fin 2)).succ))
        (hLDUtieConjC H r B hB hr hL rfl x (1 : Fin 2))
      = (1 - (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
              (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₂₁
              * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 2) (hr 2))
                  (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁)⁻¹
              * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                  (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂)
          * ((Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
                (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₂₂
            - (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
                (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₂₁
              * ((Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
                  (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₁₁)⁻¹
              * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
                  (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₁₂) := by
    -- Collapse the trivial `finCongr` reindexes; `C 1 = (1−Kc)·S1c` (`1 = lastLayer`, defeq).
    rw [finCongr_refl, finCongr_refl]
    erw [Matrix.reindex_refl_refl]
    have hCval : hLDUtieConjC H r B hB hr hL rfl x (1 : Fin 2)
        = (1 - l2KConj H r B hB hr hL rfl q) * l2S1Conj H r B hB hr hL rfl q := by
      rw [hLDUtieConjC]; exact Function.update_self _ _ _
    rw [hCval]
    -- Step A block reads at the two layers.
    have hT0 := deepBlkT_layer0_zero H r B hB hr hL (by omega) (⟨0, by omega⟩ : Fin 2) (by rfl)
    have hT1 := deepBlkT_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL) (by rfl)
    obtain ⟨hA0, _hZ0, hY0, _⟩ :=
      reindex_decode_split_toBlocks H r B hB hr hL x (⟨0, by omega⟩ : Fin 2) hT0
    obtain ⟨hA1, hZ1, hY1, hT1c⟩ :=
      reindex_decode_split_toBlocks H r B hB hr hL x (lastLayer hL) hT1
    -- `Kc = Z1c·P00c⁻¹·Y0c`; `S1c = T1c − Z1c·A1c⁻¹·Y1c` — match block-by-block.
    rw [l2KConj, l2S1Conj, hP00, l2Z1Conj, l2A1Conj, l2Y1Conj, l2T1Conj, coreLast]
    -- `Y0c`'s mid-cast collapses to `MX_0.toBlocks₁₂` (= the `Y0` decode read).
    have hY0c : l2Y0Conj H r B hB hr hL rfl q
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
            (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂ := by
      rw [l2Y0Conj, ← hY0,
        show finCongr (midWidth_eq_of_L2 H r hL rfl) = Equiv.refl _ from finCongr_refl _]
      erw [Matrix.reindex_refl_refl]
      rfl
    rw [hY0c, ← hZ1, ← hA1, ← hY1, ← hT1c]
    -- Reconcile the product-pivot column equiv `pivotThr J` (from hP00) with `rThr (H 2)` (hJfront).
    rw [hJfront, pivotThresholdSplit_frontEmbed]
    congr 1
  -- Apply the Fin-3 readback.
  exact prod_deepestM_eq_schur_ldu_readback H r B hB hr hL J hJfront Pf Qf
    hPtri hQtri hP22 hQ22 x hS3b hP11inv hQ11inv hMid11inv hA0inv hA1inv
    (hLDUtieConjC H r B hB hr hL rfl x) hC0 hC1

/-- **The conjugated core = Score at the chart point — `hLDUtieConj` DISCHARGED in-file.** The conjugated
absorbed-core energy of the moved chart point `q = deepestSplit w0 x` equals the Score-Schur frobenius
energy, with the readback-tie `hLDUtieConj` discharged via `frobSq_prod_deepestM_hLDUtieConjC_eq` (Steps
B-E) — no `hLDUtieConj` hypothesis remains. This is what the conjugated wire's `hsub4core` consumes (the
bare's `hsub4core` is a permanent W-a-false gap; the conjugated route closes it). -/
theorem deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart (H : Fin (L + 1) → ℕ)
    (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hP22 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₂₂ = 1)
    (hQ22 : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₂ = 1)
    (x : Fin (flatDim H) → ℝ)
    (hq : psiSplitRawL2CoreConj H r B hB hr hL hL2eq
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x)
      ∈ Metric.closedBall (0 : DeepestSplit H r (deepestNGauge H r))
        ((cutoffBumpConj H r B hB hr hL hDA).rIn))
    (hW : (l2WConj H r B hB hr hL hL2eq
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x)).det ≠ 0)
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁)
    (hQ11inv : Invertible (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (endpointQL H hL Qf)).toBlocks₁₁)
    (hMid11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁)
    (hA0inv : Invertible (Matrix.reindex
          (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).castSucc) (hr (⟨0, by omega⟩ : Fin L).castSucc))
          (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).succ) (hr (⟨0, by omega⟩ : Fin L).succ))
        (((paramsEquivFlat H).symm x) (⟨0, by omega⟩ : Fin L))).toBlocks₁₁)
    (hA1inv : Invertible (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc)
          (hr (lastLayer hL).castSucc)) (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₁₁) :
    deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq
          (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x))).2.1
      = frobSq ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
              * endpointQL H hL Qf)).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                * endpointQL H hL Qf)).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₂) :=
  deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score H r B hB hr hL hL2eq hDA
    (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x) hq hW _
    (frobSq_prod_deepestM_hLDUtieConjC_eq H r B hB hr hL hL2eq J hJfront Pf Qf
      hPtri hQtri hP22 hQ22 x hS3b hP11inv hQ11inv hMid11inv hA0inv hA1inv)

/-! ## S6 — the conjugated eventual composition identity `Φcore_conj ∘ psiL2Conj =ᶠ Φscore`

Mirrors the bare `comp_identity_L2`, with `deepestCoreAbsorbConj`/`psiSplitRawL2CoreConj`. Takes the two
germ-local sub-hypotheses as inputs (the bare's contract): `hsub3reg` (the `deepestEFull²`-sum invariance
under the conjugated joint move — the reg term) and `hsub4core` (the core = Score — now TRUE via the
conjugated keystones, discharged at the wire by `deepestCoreF_coreAbsorbConj_eq_prodSchur` +
`absorbedCoreConj_eq_schurCore` + `prod_deepestM_eq_schur_ldu_readback`). The single `hDA : ∀ s`
hypothesis (for `deepestCoreAbsorbConj`) supplies `hDA0`/`hDA1` to the cutoff/`psiL2Conj` layer. -/
theorem comp_identity_L2_conj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      (∑ i, (deepestEFull H r hr hL J Pf Qf
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) i) ^ 2)
        = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x))).2.1 = Score x)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    (fun x : Fin (flatDim H) → ℝ =>
        (∑ i, (regStraighten (split x)).1 i ^ 2)
          + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA (split x)).2.1)
        ∘ (psiL2Conj H r B hB hr hL hL2eq (hDA _) (hDA _) hY)
      =ᶠ[nhds wstar] Φscore := by
  have hwstar' : wstarL2 H r B hB hr hL = wstar := by rw [wstarL2, hwstar]
  -- The body's `split` is the concrete `deepestSplit ... wstar` (matching `psiL2Conj`'s internal split).
  have hsplit_eq : split = deepestSplit H r hr hL (wstarL2 H r B hB hr hL) := by
    apply Homeomorph.ext; intro w; rw [hsplit, ← wstarL2]
  -- (i) psiL2Conj = psiRawL2Conj near wstar (χc = 1 germ).
  have hgerm := psiL2Conj_eventuallyEq_psiRawL2Conj H r B hB hr hL hL2eq (hDA _) (hDA _) hY wstar hwstar
  -- The germ-local sub hyps live in `nhds (basepoint) = nhds wstar`.
  have hsub3germ := hwstar ▸ hsub3reg
  have hsub4germ := hwstar ▸ hsub4core
  filter_upwards [hgerm, hsub3germ, hsub4germ] with x hx hsub3x hsub4x
  show (∑ i, (regStraighten (split (psiL2Conj H r B hB hr hL hL2eq (hDA _) (hDA _) hY x))).1 i ^ 2)
      + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
          (split (psiL2Conj H r B hB hr hL hL2eq (hDA _) (hDA _) hY x))).2.1 = Φscore x
  rw [hx]
  -- split (psiRawL2Conj x) = psiSplitRawL2CoreConj (split x).
  have hsp : split (psiRawL2Conj H r B hB hr hL hL2eq x)
      = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [hsplit_eq, psiRawL2Conj_split H r B hB hr hL hL2eq x]
  rw [hsp, hΦscore]
  -- The reg term: invariant under the conjugated joint move (hregval + hsub3x).
  have hreg : (∑ i, (regStraighten (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x))).1 i ^ 2)
      = ∑ i, (regStraighten (split x)).1 i ^ 2 := by
    simp only [hregval]; exact hsub3x
  rw [hreg, hsub4x]

/-- **Step Ψ_conj — the L=2 CONJUGATED diffeo bridge** (`rlctAtOn Φscore = rlctAtOn Φcore_conj`).
The conjugated analogue of `deepest_diffeo_bridge_L2_impl`: assembles via the banked abstract
`rlctAtOn_diffeo_bridge_of` from S6 (`comp_identity_L2_conj`, germ) + S2 (`psiL2Conj_contDiff`) + S4
(`psiL2Conj_hasStrictFDerivAt`, the `e = refl`) + S3 (`psiL2Conj_fixpoint`). Composing with the banked
Step Θ (`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb`) closes the atom-free `hstep2 = Θ ∘ Ψ_conj`. -/
theorem deepest_diffeo_bridge_L2_conj_impl (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      (∑ i, (deepestEFull H r hr hL J Pf Qf
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) i) ^ 2)
        = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x))).2.1 = Score x)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA (split x)).2.1)
          wstar := by
  set Φcore : (Fin (flatDim H) → ℝ) → ℝ :=
    fun x => (∑ i, (regStraighten (split x)).1 i ^ 2)
      + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA (split x)).2.1 with hΦcore
  have hcomp : (fun x => Φcore (psiL2Conj H r B hB hr hL hL2eq (hDA _) (hDA _) hY x))
      =ᶠ[nhds wstar] Φscore :=
    comp_identity_L2_conj H r B hB hr hL hL2eq hDA hY hZ J Pf Qf split hsub3reg regStraighten
      hsplit hregval Score hsub4core Φscore hΦscore wstar hwstar
  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar
    (psiL2Conj H r B hB hr hL hL2eq (hDA _) (hDA _) hY)
    (ContinuousLinearEquiv.refl ℝ (Fin (flatDim H) → ℝ))
    (psiL2Conj_contDiff H r B hB hr hL hL2eq (hDA _) (hDA _) hY)
    (psiL2Conj_hasStrictFDerivAt H r B hB hr hL hL2eq (hDA _) (hDA _) hY hZ wstar hwstar)
    (psiL2Conj_fixpoint H r B hB hr hL hL2eq (hDA _) (hDA _) hY hZ wstar hwstar)
    hcomp

end DLNFibre.DLN.RLCT
