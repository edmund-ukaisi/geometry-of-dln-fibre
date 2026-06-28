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

end DLNFibre.DLN.RLCT
