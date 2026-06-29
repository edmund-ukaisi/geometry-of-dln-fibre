import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2Conj

/-! # `DLNFibre.DLN.RLCT.Validate.DeepestL2ConjReg` — the conjugated L=2 reg-energy invariance (`hsub3reg`)

The conjugated reg-energy invariance germ `deepestEFull_sq_sum_psiSplitRawL2CoreConj_eq_germ` — the LINK-1
input the conjugated diffeo bridge `deepest_diffeo_bridge_L2_conj_impl` consumes as its `hsub3reg`. Promoted
out of the `ScratchL2Close` scratch (validated there, genm-l2fin) into a public leaf module so the wire
(`DeepestL2Wiring.deepest_gauge_construction`, L=2 branch) can import it.

The germ: for `L = 2`, per `x` on the germ where `(l2A0Conj (split x)).det ≠ 0`, the conjugated joint move
`psiSplitRawL2CoreConj` leaves the `deepestEFull²`-sum reg energy invariant. The long-pole content
(`conj_hm_triple` + `conj_he2_raw` + the layer-0-shared / last-layer-X-Z-fixed block agreements + the e2
leak-kill `e2_conj_dict`) is sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

Imports `DeepestDiffeoBridgeL2Conj` only (whose closure covers `DeepestDiffeoBridgeL2`,
`DeepestGaugeConstruction`, `DeepestLDUReadback`, `DeepestSchurShiftConj`) — deliberately NOT
`DeepestL2Wiring`, so the wire can import THIS without a cycle. -/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **A clean per-layer block dictionary at the chart/moved point** (helper). For any flat point `w`,
the four blocks of `reindex (rThr s.castSucc) (rThr s.succ) (decode w)_s` are
`deepBlk· + read·(split w)` and the core, at a boundary layer (`hT`). Just `reindex_decode_split_toBlocks`
with the round-trip `deepestSplit w0 w = split w`. -/
private theorem reindex_decode_blocks_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (w : Fin (flatDim H) → ℝ) (s : Fin L)
    (hT : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0) :
    let MX := Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)
    MX.toBlocks₁₁ = deepBlkA H r B hB hr hL s + gaugeReadX H r hr hL ((split w).1, (split w).2.2) s
      ∧ MX.toBlocks₂₁ = deepBlkZ H r B hB hr hL s + gaugeReadZ H r hr hL ((split w).1, (split w).2.2) s
      ∧ MX.toBlocks₁₂ = deepBlkY H r B hB hr hL s + gaugeReadY H r hr hL ((split w).1, (split w).2.2) s
      ∧ MX.toBlocks₂₂ = (paramsEquivFlat (deepestM H r)).symm (split w).2.1 s := by
  intro MX
  obtain ⟨h11, h21, h12, h22⟩ := reindex_decode_split_toBlocks H r B hB hr hL w s hT
  rw [hsplit w] at *
  exact ⟨h11, h21, h12, h22⟩

/-- **Layer-0 SHARED under the conjugated move** (`reindex(Aψ 0) = reindex(Aq 0)`). At layer 0 (≠ last,
boundary) the conjugated move fixes every read + the core, so the reindexed decoded layer-0 is unchanged.
Stated at the `rThr`/`rThr` split (s.castSucc / s.succ). -/
private theorem reindex_decode0_conj_shared (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ) (s : Fin L) (hs : s ≠ lastLayer hL)
    (hT : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0) :
    Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (((paramsEquivFlat H).symm (split.symm
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)))) s)
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s) := by
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) with hw
  have hsw : split w = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [hw, split.apply_symm_apply]
  -- Blocks at the moved point (split w = ψ(split x)) and the chart point (split x).
  obtain ⟨hψ11, hψ21, hψ12, hψ22⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit w s hT
  obtain ⟨hq11, hq21, hq12, hq22⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit x s hT
  -- All four reads are fixed at a non-last layer.
  rw [hsw] at hψ11 hψ21 hψ12 hψ22
  rw [gaugeReadX_psiSplitRawL2CoreConj_eq] at hψ11
  rw [gaugeReadZ_psiSplitRawL2CoreConj_eq] at hψ21
  rw [gaugeReadY_psiSplitRawL2CoreConj_of_ne_eq H r B hB hr hL hL2eq (split x) s hs] at hψ12
  rw [coreRead_psiSplitRawL2CoreConj_of_ne H r B hB hr hL hL2eq (split x) s hs] at hψ22
  -- Reassemble via fromBlocks of the four (now-equal) blocks.
  rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (((paramsEquivFlat H).symm w) s)),
    ← Matrix.fromBlocks_toBlocks (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s))]
  rw [show (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₁₁
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)).toBlocks₁₁
      from by rw [hψ11, hq11]]
  rw [show (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₁₂
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)).toBlocks₁₂
      from by rw [hψ12, hq12]]
  rw [show (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₂₁
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)).toBlocks₂₁
      from by rw [hψ21, hq21]]
  rw [show (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₂₂
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)).toBlocks₂₂
      from by rw [hψ22, hq22]]

/-- **Last-layer ₁₁ agreement** under the conjugated move (`reindex(Aψ last)₁₁ = reindex(Aq last)₁₁`),
at the `rThr (H last.succ)` split (gaugeReadX fixed). -/
private theorem reindex_decodeLast_conj_b11 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ)
    (hT : (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₂₂ = 0) :
    (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm (split.symm
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)))) (lastLayer hL))).toBlocks₁₁
      = (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₁₁ := by
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) with hw
  have hsw : split w = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [hw, split.apply_symm_apply]
  obtain ⟨hψ11, _, _, _⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit w (lastLayer hL) hT
  obtain ⟨hq11, _, _, _⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit x (lastLayer hL) hT
  rw [hψ11, hsw, gaugeReadX_psiSplitRawL2CoreConj_eq, hq11]

/-- **Last-layer ₂₁ agreement** under the conjugated move (gaugeReadZ fixed). Mirror of `_b11`. -/
private theorem reindex_decodeLast_conj_b21 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ)
    (hT : (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₂₂ = 0) :
    (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm (split.symm
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)))) (lastLayer hL))).toBlocks₂₁
      = (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₂₁ := by
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) with hw
  have hsw : split w = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [hw, split.apply_symm_apply]
  obtain ⟨_, hψ21, _, _⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit w (lastLayer hL) hT
  obtain ⟨_, hq21, _, _⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit x (lastLayer hL) hT
  rw [hψ21, hsw, gaugeReadZ_psiSplitRawL2CoreConj_eq, hq21]

/-- **The e2 dictionary relation** (the {12}-leak-kill, `P01` fixed). In the `l2*Conj` dictionary:
`A0c·Y1'c + Y0c·T1'c = A0c·Y1c + Y0c·T1c`. Via `e2_regPreserve` (needs `Invertible l2A0Conj`). -/
private theorem e2_conj_dict (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hdet : (l2A0Conj H r B hB hr hL q).det ≠ 0) :
    l2A0Conj H r B hB hr hL q * l2Y1pConj H r B hB hr hL hL2eq q
        + l2Y0Conj H r B hB hr hL hL2eq q * l2T1pConj H r B hB hr hL hL2eq q
      = l2A0Conj H r B hB hr hL q * l2Y1Conj H r B hB hr hL q
        + l2Y0Conj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q := by
  letI hinv : Invertible (l2A0Conj H r B hB hr hL q) :=
    (l2A0Conj H r B hB hr hL q).invertibleOfIsUnitDet (Ne.isUnit hdet)
  -- `l2Y1pConj = l2Y1Conj + ⅟(l2A0Conj)·l2Y0Conj·(l2T1Conj − l2T1pConj)` (the def, with ⅟ for ⁻¹).
  have hY1p : l2Y1pConj H r B hB hr hL hL2eq q
      = l2Y1Conj H r B hB hr hL q
        + ⅟(l2A0Conj H r B hB hr hL q) * l2Y0Conj H r B hB hr hL hL2eq q
          * (l2T1Conj H r hr hL q - l2T1pConj H r B hB hr hL hL2eq q) := by
    rw [l2Y1pConj, invOf_eq_nonsing_inv]
  rw [hY1p]
  exact e2_regPreserve (l2A0Conj H r B hB hr hL q) (l2Y0Conj H r B hB hr hL hL2eq q)
    (l2Y1Conj H r B hB hr hL q) (l2T1Conj H r hr hL q) (l2T1pConj H r B hB hr hL hL2eq q)

/-! ### The conj hm assembly skeleton (Fin 3 / subst) — validate the two-factor + column collapse. -/

/-- **The conj `hm` triple** (at `Fin 3`) — the three `{11,12,21}` block agreements for `prod Aψ` vs
`prod Aq` in #147's `pivotThr J` form, given layer-0 shared (`h0`), last-layer X/Z fixed (`h11G`/`h21G`),
and the e2 leak-kill (`he2`). Pure block algebra via `reindex_prod_regBlocks_eq_of_e2`. -/
private theorem conj_hm_triple (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1:ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront' : J = frontEmbed H r hr)
    (Aψ Aq : Params (L := 2) H)
    (h0 : Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aψ 0)
        = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0))
    (h11G : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₁₁)
    (h21G : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₂₁)
    (he2 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₁
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₁₂
        + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₂
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₂₂
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₁
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₁₂
        + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₂
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₂₂) :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₁₁
      ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₁₂
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₁₂
      ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₂₁ := by
  -- Collapse the pivot column split to rThr (H 2) (J = frontEmbed).
  rw [hJfront', pivotThresholdSplit_frontEmbed H r hr]
  -- Two-factor unfold both products.
  rw [prodDecode_eq_two_of_L2 H Aψ, prodDecode_eq_two_of_L2 H Aq]
  -- The finCongr width-casts are rfl ⟹ Equiv.refl ⟹ identity reindex; collapse them.
  simp only [show (finCongr (rfl : H 0 = H ((0 : Fin 2)).castSucc)) = Equiv.refl _ from finCongr_refl _,
    show (finCongr (rfl : H 1 = H ((0 : Fin 2)).succ)) = Equiv.refl _ from finCongr_refl _,
    show (finCongr (rfl : H 1 = H ((1 : Fin 2)).castSucc)) = Equiv.refl _ from finCongr_refl _,
    show (finCongr (rfl : H 2 = H (Fin.last 2))) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl, Matrix.reindex_refl_refl, Matrix.reindex_refl_refl,
    Matrix.reindex_refl_refl]
  -- `Aψ 0 = Aq 0` (reindex is an Equiv on matrices; use its injectivity).
  have hAψ0 : Aψ 0 = Aq 0 :=
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))).injective h0
  rw [hAψ0]
  -- Apply the e2 engine: G0 = Aq 0, G1ψ' = Aψ 1, G1q' = Aq 1.
  exact reindex_prod_regBlocks_eq_of_e2 (rThresholdSplit r (H 0) (hr 0))
    (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
    (Aq 0) (Aq 0) (Aq 0) (Aψ 1) (Aq 1) h11G h21G he2

/-- **The he2 raw-block connector** (`Fin 3`): the raw `{11}·{12}+{12}·{22}` e2 combination of the
chart-point/moved decode blocks equals `e2_conj_dict`'s `l2*Conj` form, so it is fixed under the move.
Built at the chart point `x` (`Aq = decode x`, `Aψ = decode (split.symm (ψ (split x)))`). -/
theorem conj_he2_raw (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1:ℕ) ≤ 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ)
    (hdet0 : (l2A0Conj H r B hB hr hL (split x)).det ≠ 0) :
    let Aq : Params (L := 2) H := (paramsEquivFlat H).symm x
    let Aψ : Params (L := 2) H :=
      (paramsEquivFlat H).symm (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)))
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₁
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₁₂
        + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₂
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₂₂
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₁
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₁₂
        + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₂
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₂₂ := by
  intro Aq Aψ
  set q := split x with hq
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl q) with hw
  have hsw : split w = psiSplitRawL2CoreConj H r B hB hr hL rfl q := by
    rw [hw, split.apply_symm_apply]
  -- Unfold the let-bound Aq/Aψ; the goal is now in explicit `(paramsEquivFlat H).symm …` form (literal
  -- indices `0`/`1`, widths `H 0`/`H 1`/`H 2`).
  show (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁
        * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
            (((paramsEquivFlat H).symm w) (1 : Fin 2))).toBlocks₁₂
      + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂
        * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
            (((paramsEquivFlat H).symm w) (1 : Fin 2))).toBlocks₂₂
    = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁
        * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
            (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₁₂
      + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂
        * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
            (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₂₂
  -- The boundary deepBlkT facts (both layers, L=2), at literal indices.
  have hT0 : (Matrix.reindex (rThresholdSplit r (H ((0 : Fin 2)).castSucc) (hr _))
      (rThresholdSplit r (H ((0 : Fin 2)).succ) (hr _))
      (deepestPoint H r B hB hr hL ((0 : Fin 2)))).toBlocks₂₂ = 0 :=
    deepBlkT_layer0_zero H r B hB hr hL (by omega) ((0 : Fin 2)) rfl
  have hTlast : (Matrix.reindex (rThresholdSplit r (H ((1 : Fin 2)).castSucc) (hr _))
      (rThresholdSplit r (H ((1 : Fin 2)).succ) (hr _))
      (deepestPoint H r B hB hr hL ((1 : Fin 2)))).toBlocks₂₂ = 0 :=
    deepBlkT_layerLast_zero H r B hB hr hL (by omega) ((1 : Fin 2)) rfl
  -- Chart/moved-point block dictionaries at literal indices (widths come out `H 0`/`H 1`/`H 2`).
  obtain ⟨hAq0_11, _, hAq0_12, _⟩ :=
    reindex_decode_blocks_at H r B hB hr hL split hsplit x ((0 : Fin 2)) hT0
  obtain ⟨_, _, hAq1_12, hAq1_22⟩ :=
    reindex_decode_blocks_at H r B hB hr hL split hsplit x ((1 : Fin 2)) hTlast
  obtain ⟨_, _, hAψ1_12, hAψ1_22⟩ :=
    reindex_decode_blocks_at H r B hB hr hL split hsplit w ((1 : Fin 2)) hTlast
  -- Collapse the `Fin.castSucc/.succ` width-indices to the literal `H 0`/`H 1`/`H 2` the goal uses.
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one, Fin.succ_one_eq_two]
    at hAq0_11 hAq0_12 hAq1_12 hAq1_22 hAψ1_12 hAψ1_22
  -- Literal-`1` forms of the two conj readbacks: `exact`-transport handles `lastLayer hL ≡ 1` (defeq),
  -- where `▸`/`rw` fail on the dependent codomain width.
  have hRY : gaugeReadY H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL rfl q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL rfl q).2.2) (1 : Fin 2)
      = l2Y1pReadConj H r B hB hr hL rfl q :=
    gaugeReadY_psiSplitRawL2CoreConj_last_eq H r B hB hr hL rfl q
  have hRT : (paramsEquivFlat (deepestM H r)).symm
        (psiSplitRawL2CoreConj H r B hB hr hL rfl q).2.1 (1 : Fin 2)
      = l2T1pConj H r B hB hr hL rfl q :=
    coreRead_psiSplitRawL2CoreConj_last H r B hB hr hL rfl q
  -- Rewrite the moved-layer last blocks via the conj readbacks (sw round-trip).
  rw [hsw, hRY] at hAψ1_12
  rw [hsw, hRT] at hAψ1_22
  -- Collapse the chart-point `split x` to `q`.
  rw [← hq] at hAq0_11 hAq0_12 hAq1_12 hAq1_22
  -- Translate the six raw block-haves into `l2*Conj` dictionary terms.
  --  Last-layer dict terms (`l2Y1Conj`/`l2T1Conj`) are typed at `lastLayer hL`; the literal-`1` block
  --  matches them by defeq, so `exact` closes each (`rw` then `rfl` would mismatch the index syntactically).
  -- `lastLayer hL = (1 : Fin 2)` (defeq) — bridge the literal-`1` block indices to the `l2*Conj` defs'.
  have hlast : lastLayer hL = (1 : Fin 2) := by simp only [lastLayer]; rfl
  have hY0c : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂
      = l2Y0Conj H r B hB hr hL rfl q :=
    hAq0_12.trans (by
      rw [l2Y0Conj, show finCongr (midWidth_eq_of_L2 H r hL rfl) = Equiv.refl _ from finCongr_refl _]
      erw [Matrix.reindex_refl_refl]
      rfl)
  have hA0c : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁
      = l2A0Conj H r B hB hr hL q := hAq0_11.trans rfl
  have hY1pc : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
          (((paramsEquivFlat H).symm w) (1 : Fin 2))).toBlocks₁₂
      = l2Y1pConj H r B hB hr hL rfl q :=
    hAψ1_12.trans (by
      -- `deepBlkY 1` is defeq `deepBlkY (lastLayer hL)`; `show` aligns the index so the unfold + abel fire.
      show deepBlkY H r B hB hr hL (lastLayer hL) + l2Y1pReadConj H r B hB hr hL rfl q
          = l2Y1pConj H r B hB hr hL rfl q
      rw [l2Y1pConj, l2Y1pReadConj, l2Y1Conj]; abel)
  have hT1pc : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
          (((paramsEquivFlat H).symm w) (1 : Fin 2))).toBlocks₂₂
      = l2T1pConj H r B hB hr hL rfl q := hAψ1_22.trans rfl
  have hY1c : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
          (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₁₂
      = l2Y1Conj H r B hB hr hL q := hAq1_12.trans rfl
  have hT1c : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
          (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₂₂
      = l2T1Conj H r hr hL q := hAq1_22.trans rfl
  -- Rewrite the goal into the `l2*Conj` dictionary form and apply e2_conj_dict.
  rw [hA0c, hY0c, hY1pc, hT1pc, hY1c, hT1c]
  exact e2_conj_dict H r B hB hr hL rfl q hdet0

/-- **The conjugated reg-energy invariance `hsub3reg`** (the long pole) — germ-local. Mirrors #147,
with `psiSplitRawL2CoreConj` as the moved point. Per-x on the germ (where `l2A0Conj (split x)` is a
unit), the three `hm·` block agreements hold (decode↔read + layer-0 shared + last-layer X/Z fixed +
the e2 leak-kill), so #147 gives the `deepestEFull²`-sum invariance. -/
theorem deepestEFull_sq_sum_psiSplitRawL2CoreConj_eq_germ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri' : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri' : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
      Pf s * (deepestPoint H r B hB hr hL s) * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hPfL : Pf (lastLayer hL)
      = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hcorner' : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hinterface : ∀ (s : Fin L) (_ : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc))
          (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc)) ℝ))
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (x : Fin (flatDim H) → ℝ)
    (hdet0 : (l2A0Conj H r B hB hr hL (split x)).det ≠ 0) :
    (∑ i, (deepestEFull H r hr hL J Pf Qf
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) i) ^ 2)
      = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2 := by
  -- Specialize to `L = 2` up front so `conj_hm_triple`/`conj_he2_raw` (stated at `Fin 3`) apply directly.
  subst hL2eq
  -- The two framed raw params: Aq = decode x, Aψ = decode (split.symm (ψ (split x))).
  set Aq : Params H := (paramsEquivFlat H).symm x with hAq
  set Aψ : Params H :=
    (paramsEquivFlat H).symm (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)))
    with hAψ
  -- Frame identities (§iii) for both points.
  have hframeq : ∀ s : Fin 2,
      framedParamsPivot H r hr hL J Pf Qf (split x) s = Pf s * Aq s * Qf s := by
    intro s; rw [hsplit x]
    exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner' x s
  have hframeψ : ∀ s : Fin 2,
      framedParamsPivot H r hr hL J Pf Qf
          (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)) s
        = Pf s * Aψ s * Qf s := by
    intro s
    have hrt : psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)
        = split (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x))) :=
      (split.apply_symm_apply _).symm
    rw [hrt, hsplit (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)))]
    exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner'
      (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x))) s
  -- The four hm-inputs (all GREEN standalone): layer-0 shared (`h0`), last-layer X/Z fixed
  -- (`h11G`/`h21G`), and the e2 leak-kill (`he2`, the raw↔dict connector). Then `conj_hm_triple` (Fin 3)
  -- assembles the three `{11,12,21}` block agreements `reindex(prod Aψ) = reindex(prod Aq)`.
  have h0 := reindex_decode0_conj_shared H r B hB hr hL rfl split hsplit x (⟨0, by omega⟩ : Fin 2)
    (Fin.ne_of_val_ne (by simp only [lastLayer]; omega))
    (deepBlkT_layer0_zero H r B hB hr hL (by omega) (⟨0, by omega⟩ : Fin 2) rfl)
  have h11G := reindex_decodeLast_conj_b11 H r B hB hr hL rfl split hsplit x
    (deepBlkT_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL) (by simp [lastLayer]))
  have h21G := reindex_decodeLast_conj_b21 H r B hB hr hL rfl split hsplit x
    (deepBlkT_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL) (by simp [lastLayer]))
  have he2 := conj_he2_raw H r B hB hr hL split hsplit x hdet0
  -- Reconcile the ingredient indices (`⟨0,_⟩`/`lastLayer hL`) to `conj_hm_triple`'s literals
  -- (`0`/`1 : Fin 2`); all defeq, so `convert` closes the residual index/width casts.
  obtain ⟨hm11, hm12, hm21⟩ :
      (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₁₁
          = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₁₁
        ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₁₂
          = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₁₂
        ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₂₁
          = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₂₁ :=
    conj_hm_triple H r B hB hr hL J hJfront' Aψ Aq h0 h11G h21G he2
  obtain ⟨h11, h12, h21⟩ :=
    resid_regBlocks_eq_of_mid_agree H r B hr hL J Pf Qf Aψ Aq hPtri' hQtri' hm11 hm12 hm21
  exact deepestEFull_sq_sum_eq_of_resid_blocks H r B hr hL J Pf Qf
    (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)) (split x) Aψ Aq
    hframeψ hframeq hinterface hS3b h11 h12 h21

/-- **LINK-1 input — the conjugated `hsub3reg` germ in `∀ᶠ` form** (the shape
`deepest_diffeo_bridge_L2_conj_impl` consumes). Wraps the per-`x` germ
(`deepestEFull_sq_sum_psiSplitRawL2CoreConj_eq_germ`) over the neighborhood of `wstar` where
`det (l2A0Conj (split x)) ≠ 0`. That neighborhood exists: `det ∘ l2A0Conj ∘ split` is continuous, and at
`wstar` (`split wstar = 0`) it is `det (l2A0Conj 0) ≠ 0` (`l2A0Conj_det_ne_zero` from the pivot-base unit
`hDA0`). The `∀ᶠ` is exactly LINK-1's `hsub3reg`; LINK-1 is then `deepest_diffeo_bridge_L2_conj_impl`
applied with this + the conjugated `hsub4core` + `regStraighten`/`Score`/etc. -/
theorem hsub3reg_conj_germ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri' : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri' : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
      Pf s * (deepestPoint H r B hB hr hL s) * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hPfL : Pf (lastLayer hL)
      = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hcorner' : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hsplit_base : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
      = (0 : DeepestSplit H r (deepestNGauge H r)))
    (hinterface : ∀ (s : Fin L) (_ : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc))
          (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc)) ℝ))
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) :
    ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      (∑ i, (deepestEFull H r hr hL J Pf Qf
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) i) ^ 2)
        = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2 := by
  -- `split → 0` at the basepoint (split continuous, `split basepoint = 0`).
  have hsplit_tend : Filter.Tendsto split
      (nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)))
      (nhds (0 : DeepestSplit H r (deepestNGauge H r))) := by
    have h := (split.continuous.continuousAt
      (x := (paramsEquivFlat H) (deepestPoint H r B hB hr hL))).tendsto
    rwa [hsplit_base] at h
  -- `det (l2A0Conj ·)` is continuous and nonzero at `0` (the pivot-base unit) ⟹ `∀ᶠ` nonzero near `0`.
  have hA0c : ContinuousAt (fun q => (l2A0Conj H r B hB hr hL q).det)
      (0 : DeepestSplit H r (deepestNGauge H r)) :=
    (contDiffAt_matrix_det_of_entries
      (fun a b => (contDiff_l2A0Conj_entry H r B hB hr hL a b).contDiffAt)).continuousAt
  have hdet0_ne : (l2A0Conj H r B hB hr hL (0 : DeepestSplit H r (deepestNGauge H r))).det ≠ 0 :=
    l2A0Conj_det_ne_zero H r B hB hr hL hDA0
  have hdetnhds : ∀ᶠ q : DeepestSplit H r (deepestNGauge H r) in nhds 0,
      (l2A0Conj H r B hB hr hL q).det ≠ 0 :=
    hA0c.eventually_ne hdet0_ne
  -- Pull back along `split` to a neighborhood of the basepoint.
  have hdetgerm : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
      nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      (l2A0Conj H r B hB hr hL (split x)).det ≠ 0 :=
    hsplit_tend.eventually hdetnhds
  -- Apply the per-`x` germ on the det-nonzero neighborhood.
  filter_upwards [hdetgerm] with x hdet0
  exact deepestEFull_sq_sum_psiSplitRawL2CoreConj_eq_germ H r B hB hr hL hL2eq J hJfront' Pf Qf
    hPtri' hQtri' hNF hPfL hcorner' split hsplit hinterface hS3b x hdet0

/-! ### The pivot-base unit discharges `hDA = IsUnit (deepBlkA s)` at the deepest point (L=2 seam).

These promote the `ScratchL2Close` step-(c) `example` contracts to named lemmas the wire can call, so the
conj diffeo's `hDA` hypothesis is DISCHARGED at the deepest point from the wire's own data (`htop` +
the block-triangular pivot bundle) — NOT a foundation gap for `L = 2`. -/

/-- **Layer-0 pivot base is a unit** (`deepBlkA 0` is the leading `r×r` block, a unit by the row-WLOG
rank `htop`). -/
theorem deepBlkA0_isUnit_of_htop (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r) :
    IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)) := by
  have hlead := deepestPoint_leadingBlock_isUnit H r B hB hr hL hL2 htop
  have heq : deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)
      = (deepestPoint H r B hB hr hL (⟨0, by omega⟩ : Fin L)).submatrix
        (Fin.castLE (hr (⟨0, by omega⟩ : Fin L).castSucc) : Fin r → Fin (H (⟨0, by omega⟩ : Fin L).castSucc))
        (Fin.castLE (hr (⟨0, by omega⟩ : Fin L).succ) : Fin r → Fin (H (⟨0, by omega⟩ : Fin L).succ)) := by
    apply Matrix.ext
    intro i j
    show (Matrix.reindex (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).castSucc) (hr _))
        (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).succ) (hr _))
        (deepestPoint H r B hB hr hL (⟨0, by omega⟩ : Fin L))).toBlocks₁₁ i j = _
    simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      rThresholdSplit_symm_inl]
  rw [heq]; exact hlead

/-- **Last-layer pivot base is a unit**, via the corner identity `(reindex(dP·Qf))₁₁ = 1` + the
block-upper `Qf` (`hQUpper : Qf₂₁ = 0`) ⟹ `deepBlkA_last · M = 1` ⟹ `det` a unit. Supplied at the wire
by the block-triangular pivot bundle (`hJfront'`/`hcorner`/`hQtri`). -/
theorem deepBlkA_last_isUnit_of_bundle (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hcorner : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hQUpper : (Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₁ = 0) :
    IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)) := by
  set eR := rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc) with heR
  set eMid := pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J) with heMid
  have hblk := reindex_mul_fromBlocks eR eMid eMid
    (deepestPoint H r B hB hr hL (lastLayer hL)) (Qf (lastLayer hL))
  have hc11 : (Matrix.reindex eR eMid
      ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))).toBlocks₁₁
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    rw [show Matrix.reindex eR eMid
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 from hcorner,
      Matrix.toBlocks_fromBlocks₁₁]
  have hkey : (Matrix.reindex eR eMid (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₁₁
      * (Matrix.reindex eMid eMid (Qf (lastLayer hL))).toBlocks₁₁ = 1 := by
    have h := hc11
    rw [hblk, Matrix.toBlocks_fromBlocks₁₁, hQUpper, Matrix.mul_zero, add_zero] at h
    exact h
  have hAeq : (Matrix.reindex eR eMid (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₁₁
      = deepBlkA H r B hB hr hL (lastLayer hL) := by
    have hpiv : eMid = rThresholdSplit r (H ((lastLayer hL).succ)) (hr ((lastLayer hL).succ)) := by
      rw [heMid, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL]
    rw [hpiv]; rfl
  rw [hAeq] at hkey
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : (deepBlkA H r B hB hr hL (lastLayer hL)).det
      * (Matrix.reindex eMid eMid (Qf (lastLayer hL))).toBlocks₁₁.det = 1 := by
    rw [← Matrix.det_mul, hkey, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ hdet

/-- **`hDA = ∀ s, IsUnit (deepBlkA s)` at `L = 2`** — assembled from the two boundary units (`s = 0` and
`s = lastLayer`, the only two layers). -/
theorem deepBlkA_isUnit_of_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDAlast : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL))) :
    ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s) := by
  intro s
  rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
  · have : s = (⟨0, by omega⟩ : Fin L) := Fin.ext hs0
    rw [this]; exact hDA0
  · have : s = lastLayer hL := by
      apply Fin.ext; simp only [lastLayer]
      have := s.isLt; omega
    rw [this]; exact hDAlast

end DLNFibre.DLN.RLCT
