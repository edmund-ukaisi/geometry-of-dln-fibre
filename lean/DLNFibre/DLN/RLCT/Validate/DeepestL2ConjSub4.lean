import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2Conj
import DLNFibre.DLN.RLCT.Validate.DeepestL2ConjReg
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj
import DLNFibre.DLN.RLCT.Validate.DeepestL2ConjSmooth

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestL2ConjSub4` — the CONJ `hsub4core` germ (L=2)

The conjugated `hsub4core` germ the L=2 wire (`deepest_gauge_construction`) consumes for the BANKED
assembled bridge `deepest_diffeo_bridge_L2_assembled`. Mirrors `hsub3reg_conj_germ` (the reg germ):
peels the per-`x` keystone `deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart` over
a neighbourhood of the basepoint, building the seven `x`-dependent germ inputs the keystone needs
(`hq` closedBall, `hW` det≠0, and the five `Invertible`-of-`toBlocks₁₁` facts) via
continuity-at-basepoint + nonzero-at-basepoint + pull-back-along-`split` + `filter_upwards`.

The `Score` of the conclusion IS the wire's bare `Score` lambda (the Schur-frobenius of
`reindex(endpointP0·(prod(decode x) − B)·endpointQL)`), so the wire's `hΦscore` holds for it; the
LHS is the CONJ `deepestCoreAbsorbConj ∘ psiSplitRawL2CoreConj` shape, matching the assembled
bridge's `hsub4core`.

Sorry-free, axiom-clean target `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- The `(2,1)`-block of a reindexed identity vanishes (`reindex e e 1 = 1`, `1.toBlocks₂₁ = 0`). -/
theorem reindex_one_toBlocks₂₁_zero {n r m : ℕ} (e : Fin n ≃ Fin r ⊕ Fin m) :
    (Matrix.reindex e e (1 : Matrix (Fin n) (Fin n) ℝ)).toBlocks₂₁ = 0 := by
  ext i j
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Matrix.zero_apply]
  rw [if_neg]
  exact fun h => Sum.inr_ne_inl (e.symm.injective h)

/-- The `(1,2)`-block of a reindexed identity vanishes. -/
theorem reindex_one_toBlocks₁₂_zero {n r m : ℕ} (e : Fin n ≃ Fin r ⊕ Fin m) :
    (Matrix.reindex e e (1 : Matrix (Fin n) (Fin n) ℝ)).toBlocks₁₂ = 0 := by
  ext i j
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Matrix.zero_apply]
  rw [if_neg]
  exact fun h => Sum.inl_ne_inr (e.symm.injective h)

/-- **The `(2,2)`-block `= 1` cast-transport** (the `▸`-cast analogue of `reindex_rThr_toBlocks21_zero_cast`
for the `endpointQL` width transport). -/
theorem reindex_rThr_toBlocks22_one_cast {L : ℕ} (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) {a b : Fin (L + 1)} (e : a = b)
    (M : Matrix (Fin (H a)) (Fin (H a)) ℝ)
    (hM : (Matrix.reindex (rThresholdSplit r (H a) (hr a)) (rThresholdSplit r (H a) (hr a)) M).toBlocks₂₂
      = 1) :
    (Matrix.reindex (rThresholdSplit r (H b) (hr b)) (rThresholdSplit r (H b) (hr b))
        (e ▸ M)).toBlocks₂₂ = 1 := by
  subst e; exact hM

/-- **A block-triangular endpoint frame has invertible `(1,1)`-block.** If `M : Matrix (r⊕m) (r⊕m)` is a
unit with identity `(2,2)`-block and either off-diagonal block zero, then its `(1,1)`-block is invertible:
the block-triangular determinant is `det M = det M₁₁ · det 1 = det M₁₁`, and `IsUnit M ⟹ IsUnit (det M)`. -/
noncomputable def endpoint_toBlocks₁₁_invertible_of_blockTri {r m : ℕ}
    (M : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) ℝ) (hM : IsUnit M)
    (h22 : M.toBlocks₂₂ = 1) (htri : M.toBlocks₁₂ = 0 ∨ M.toBlocks₂₁ = 0) :
    Invertible M.toBlocks₁₁ := by
  have hdet : M.det = M.toBlocks₁₁.det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rcases htri with h12 | h21
    · rw [h12, h22, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    · rw [h21, h22, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  have : IsUnit M.toBlocks₁₁.det := hdet ▸ (Matrix.isUnit_iff_isUnit_det M).mp hM
  exact M.toBlocks₁₁.invertibleOfIsUnitDet this

/-- **The CONJ `hsub4core` germ (L=2).** For `x` near the basepoint, the conjugated absorbed-core
energy of the moved chart point equals the wire's bare Score (the Schur-frobenius of the framed
`prod(decode x) − B`). Peels `deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart`
over a neighbourhood, discharging
its seven `x`-dependent germ inputs from continuity + the basepoint units. -/
theorem hsub4core_conj_germ (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2) (hL2eq : (2 : ℕ) = 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin 2) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hP22 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₂₂ = 1)
    (hQ22 : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (endpointQL H hL Qf)).toBlocks₂₂ = 1)
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁)
    (hQ11inv : Invertible (Matrix.reindex (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (endpointQL H hL Qf)).toBlocks₁₁)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hScoreDef : Score = fun w => frobSqMat ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
          (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
            * endpointQL H hL Qf)).toBlocks₂₂
        - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
              * endpointQL H hL Qf)).toBlocks₂₁
          * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
                * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
          * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
                * endpointQL H hL Qf)).toBlocks₁₂)) :
    ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x))).2.1 = Score x := by
  set w0 := (paramsEquivFlat H) (deepestPoint H r B hB hr hL) with hw0
  -- `hDA0`/`hDA1` from `hDA`.
  have hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin 2)) := hDA _
  have hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)) := hDA _
  -- `split → 0` at the basepoint (split continuous, `split basepoint = 0`).
  have hsplit_base : split w0 = (0 : DeepestSplit H r (deepestNGauge H r)) := by
    rw [hsplit w0, hw0]
    exact (deepestSplit_mp_basepoint H r hr hL w0).2
  have hsplit_tend : Filter.Tendsto split (nhds w0)
      (nhds (0 : DeepestSplit H r (deepestNGauge H r))) := by
    have h := (split.continuous.continuousAt (x := w0)).tendsto
    rwa [hsplit_base] at h
  -- (1) hq germ: `psiSplitRawL2CoreConj (split x) ∈ closedBall 0 rIn` near `w0`.
  have hpsiCA : ContinuousAt (psiSplitRawL2CoreConj H r B hB hr hL hL2eq)
      (0 : DeepestSplit H r (deepestNGauge H r)) := by
    have hδ : ContinuousAt (fun q => psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q)
        (0 : DeepestSplit H r (deepestNGauge H r)) :=
      (hasStrictFDerivAt_psiSplitDeltaL2CoreConj_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ).continuousAt
    have hid : psiSplitRawL2CoreConj H r B hB hr hL hL2eq
        = fun q => (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q) + q := by
      funext q; rw [sub_add_cancel]
    rw [hid]; exact hδ.add continuousAt_id
  have htend_psi : Filter.Tendsto (fun x => psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x))
      (nhds w0) (nhds 0) := by
    have hcomp : ContinuousAt (fun x => psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) w0 :=
      (hsplit_base ▸ hpsiCA).comp split.continuous.continuousAt
    have h0 : psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split w0) = 0 := by
      rw [hsplit_base]; exact psiSplitRawL2CoreConj_zero H r B hB hr hL hL2eq hY hZ
    rw [← h0]; exact hcomp
  have hqgerm : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds w0,
      psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)
        ∈ Metric.closedBall (0 : DeepestSplit H r (deepestNGauge H r))
          ((cutoffBumpConj H r B hB hr hL hDA).rIn) :=
    htend_psi (Metric.closedBall_mem_nhds 0 (cutoffBumpConj H r B hB hr hL hDA).rIn_pos)
  -- (2) hW germ: `det (l2WConj (split x)) ≠ 0` near `w0`.
  have hWCA : ContinuousAt (fun q => (l2WConj H r B hB hr hL hL2eq q).det)
      (0 : DeepestSplit H r (deepestNGauge H r)) :=
    (contDiffAt_matrix_det_of_entries
      (fun a b => (contDiffAt_l2WConj_entry H r B hB hr hL hL2eq hDA0 hDA1 a b))).continuousAt
  have hW0_ne : (l2WConj H r B hB hr hL hL2eq (0 : DeepestSplit H r (deepestNGauge H r))).det ≠ 0 := by
    rw [l2WConj_zero H r B hB hr hL hL2eq hZ, Matrix.det_one]; exact one_ne_zero
  have hWgerm : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds w0,
      (l2WConj H r B hB hr hL hL2eq (split x)).det ≠ 0 :=
    hsplit_tend.eventually (hWCA.eventually_ne hW0_ne)
  -- `decode w0 = deepestPoint` (the basepoint round-trip).
  have hdecode : (paramsEquivFlat H).symm w0 = deepestPoint H r B hB hr hL := by
    rw [hw0]; exact (paramsEquivFlat H).symm_apply_apply _
  -- (3-5) the three `Invertible`-of-`toBlocks₁₁` germs: each block is continuous in `x`, and at the
  -- basepoint the block is a unit (`deepBlkA` for the per-layer ones; `deepBlkA0·deepBlkA1` for the
  -- product pivot, via `Y0 = 0` at the boundary). `eventually_ne` ⟹ ∀ᶠ det≠0, then `invertibleOfIsUnitDet`.
  -- hA0inv germ.
  have hA0germ : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds w0,
      (Matrix.reindex
          (rThresholdSplit r (H (⟨0, by omega⟩ : Fin 2).castSucc) (hr (⟨0, by omega⟩ : Fin 2).castSucc))
          (rThresholdSplit r (H (⟨0, by omega⟩ : Fin 2).succ) (hr (⟨0, by omega⟩ : Fin 2).succ))
        (((paramsEquivFlat H).symm x) (⟨0, by omega⟩ : Fin 2))).toBlocks₁₁.det ≠ 0 := by
    have hcont : Continuous (fun x => (Matrix.reindex
        (rThresholdSplit r (H (⟨0, by omega⟩ : Fin 2).castSucc) (hr (⟨0, by omega⟩ : Fin 2).castSucc))
        (rThresholdSplit r (H (⟨0, by omega⟩ : Fin 2).succ) (hr (⟨0, by omega⟩ : Fin 2).succ))
        (((paramsEquivFlat H).symm x) (⟨0, by omega⟩ : Fin 2))).toBlocks₁₁.det) :=
      ((((continuous_apply (⟨0, by omega⟩ : Fin 2)).comp
        (continuous_paramsEquivFlat_symm H)).matrix_reindex _ _).matrix_submatrix _ _).matrix_det
    have hbase : (Matrix.reindex
        (rThresholdSplit r (H (⟨0, by omega⟩ : Fin 2).castSucc) (hr (⟨0, by omega⟩ : Fin 2).castSucc))
        (rThresholdSplit r (H (⟨0, by omega⟩ : Fin 2).succ) (hr (⟨0, by omega⟩ : Fin 2).succ))
        (((paramsEquivFlat H).symm w0) (⟨0, by omega⟩ : Fin 2))).toBlocks₁₁.det ≠ 0 := by
      rw [hdecode]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (hDA (⟨0, by omega⟩ : Fin 2))).ne_zero
    exact hcont.continuousAt.eventually_ne hbase
  -- hA1inv germ.
  have hA1germ : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds w0,
      (Matrix.reindex
          (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
          (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₁₁.det ≠ 0 := by
    have hcont : Continuous (fun x => (Matrix.reindex
        (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₁₁.det) :=
      ((((continuous_apply (lastLayer hL)).comp
        (continuous_paramsEquivFlat_symm H)).matrix_reindex _ _).matrix_submatrix _ _).matrix_det
    have hbase : (Matrix.reindex
        (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm w0) (lastLayer hL))).toBlocks₁₁.det ≠ 0 := by
      rw [hdecode]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (hDA (lastLayer hL))).ne_zero
    exact hcont.continuousAt.eventually_ne hbase
  -- hMid11inv germ: the product pivot `(reindex rThr pivotThr (prod (decode x))).toBlocks₁₁`. At the
  -- basepoint `prod (decode w0) = B`; under `J = frontEmbed`, `pivotThr ↦ rThr`, and `B = L0·L1` framed
  -- with `Y0 = 0` (`hY`) gives `toBlocks₁₁ = deepBlkA0·deepBlkA1`, a product of units.
  have hMidgerm : ∀ᶠ x : (Fin (flatDim H) → ℝ) in nhds w0,
      (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁.det ≠ 0 := by
    -- `prod ∘ symm` continuity via `continuous_Mw` (with `P0 = 1`, `QL = 1`, `B = 0`): `1·(prod−0)·1 = prod`.
    have hprodMw : Continuous (fun x : Fin (flatDim H) → ℝ => Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (prod H ((paramsEquivFlat H).symm x))) := by
      have h := continuous_Mw H r (0 : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
        (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) (1 : Matrix (Fin (H (Fin.last 2))) (Fin (H (Fin.last 2))) ℝ)
        (rThresholdSplit r (H 0) (hr 0)) (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
      simpa only [Matrix.one_mul, Matrix.mul_one, sub_zero] using h
    have hcont : Continuous (fun x => (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁.det) :=
      (hprodMw.matrix_submatrix _ _).matrix_det
    have hbase : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (prod H ((paramsEquivFlat H).symm w0))).toBlocks₁₁.det ≠ 0 := by
      -- `decode w0 = deepestPoint`; `J = frontEmbed` collapses `pivotThr J ↦ rThr (H 2)`.
      rw [hdecode]
      have heC : pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J
          = rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) := by
        rw [hJfront]; exact pivotThresholdSplit_frontEmbed H r hr
      rw [heC]
      -- `prod deepestPoint = L0 · L1` (the two-layer unfold, `Fin 3`).
      set L0 : Matrix (Fin (H 0)) (Fin (H 1)) ℝ := (deepestPoint H r B hB hr hL) (0 : Fin 2) with hL0
      set L1 : Matrix (Fin (H 1)) (Fin (H 2)) ℝ := (deepestPoint H r B hB hr hL) (1 : Fin 2) with hL1
      have hMidfac : prod H (deepestPoint H r B hB hr hL) = L0 * L1 := by
        rw [prodDecode_eq_two_of_L2 H (deepestPoint H r B hB hr hL)]
        simp only [finCongr_refl, Matrix.reindex_refl_refl, hL0, hL1]
      rw [hMidfac]
      -- The block-mult `toBlocks₁₁ = A0·A1 + Y0·Z1` (`reindex_mul_fromBlocks`, `eMid = rThr (H 1)`).
      have hblk := reindex_mul_fromBlocks (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2))) L0 L1
      -- `A0 = deepBlkA 0` (def), `Y0 = deepBlkY 0 = 0` (hY), `A1 = deepBlkA 1` (def, `Fin.last 2 = (1).succ`).
      have hA0 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) L0).toBlocks₁₁
          = deepBlkA H r B hB hr hL (0 : Fin 2) := rfl
      have hY0 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) L0).toBlocks₁₂
          = 0 := by
        show deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin 2) = 0
        exact hY
      have hA1 : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1))
          (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2))) L1).toBlocks₁₁
          = deepBlkA H r B hB hr hL (lastLayer hL) := by
        rw [show lastLayer hL = (1 : Fin 2) from rfl]; rfl
      have h11 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2))) (L0 * L1)).toBlocks₁₁
          = deepBlkA H r B hB hr hL (0 : Fin 2) * deepBlkA H r B hB hr hL (lastLayer hL) := by
        have hb11 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2))) (L0 * L1)).toBlocks₁₁
            = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) L0).toBlocks₁₁
                * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1))
                    (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2))) L1).toBlocks₁₁
              + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) L0).toBlocks₁₂
                * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1))
                    (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2))) L1).toBlocks₂₁ :=
          congrArg Matrix.toBlocks₁₁ hblk |>.trans (Matrix.toBlocks_fromBlocks₁₁ _ _ _ _)
        rw [hb11, hA0, hY0, hA1, Matrix.zero_mul, add_zero]
      rw [h11]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp
        ((hDA (0 : Fin 2)).mul (hDA (lastLayer hL)))).ne_zero
    exact hcont.continuousAt.eventually_ne hbase
  -- Assemble: `filter_upwards` all germs, rewrite `split x ↦ deepestSplit w0 x`, apply the keystone.
  filter_upwards [hqgerm, hWgerm, hA0germ, hA1germ, hMidgerm] with x hq hW hA0x hA1x hMidx
  -- The wire's `split x` IS `deepestSplit w0 x` (`hsplit x` + `w0` defn).
  have hsx : split x = deepestSplit H r hr hL w0 x := by rw [hsplit x, hw0]
  -- Recast the germs to the `deepestSplit w0 x` argument the keystone takes.
  rw [hsx] at hq hW ⊢
  -- The five invertibles (det≠0 ⟹ Invertible).
  letI hA0inv : Invertible (Matrix.reindex
      (rThresholdSplit r (H (⟨0, by omega⟩ : Fin 2).castSucc) (hr (⟨0, by omega⟩ : Fin 2).castSucc))
      (rThresholdSplit r (H (⟨0, by omega⟩ : Fin 2).succ) (hr (⟨0, by omega⟩ : Fin 2).succ))
      (((paramsEquivFlat H).symm x) (⟨0, by omega⟩ : Fin 2))).toBlocks₁₁ :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hA0x)
  letI hA1inv : Invertible (Matrix.reindex
      (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
      (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
      (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₁₁ :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hA1x)
  letI hMid11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
      (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
      (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁ :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hMidx)
  rw [hScoreDef]
  exact deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart H r B hB hr hL hL2eq hDA
    J hJfront Pf Qf hPtri hQtri hP22 hQ22 x hq hW hS3b hP11inv hQ11inv hMid11inv hA0inv hA1inv


/-! ## LINK-2 + the assembled bridge (relocated from ScratchL2Link2 — wire-importable home). -/

/-- **The Θ-peel half of LINK-2 (BANKED, sorry-free).** Peeling the MP det-1 core-shear `Θ = thetaConj`
off the WHOLE sum (`rlctAtOn_comp_homeomorph` + `bareAbsorb_thetaConj_eq_conjAbsorb`): the bare absorbed-core
RLCT equals the conjugated one with the reg argument pre-composed by `Θ`. Discharges the bare side of LINK-2;
the residual is the single reg-argument swap `Θ q ↦ q` (the `ρ`-residual). -/
theorem link2_thetaPeel_half (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r)) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, (regStraighten (thetaConj H r B hB hr hL hDA q)).1 i ^ 2)
            + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, (regStraighten q).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  set Θ := thetaConj H r B hB hr hL hDA with hΘ
  have hΘmp : MeasurePreserving Θ volume volume := by
    rw [hΘ, thetaConj]
    exact measurePreserving_coreShear (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
      (shiftDiffConj H r B hB hr hL hDA) (continuous_shiftDiffConj H r B hB hr hL hDA)
  have hΘ0 : Θ 0 = 0 := by
    rw [hΘ, thetaConj]
    refine coreShearHomeo_basepoint (shiftDiffConj H r B hB hr hL hDA)
      (continuous_shiftDiffConj H r B hB hr hL hDA) ?_
    show shiftDiffConj H r B hB hr hL hDA (0, 0) = 0
    rw [shiftDiffConj,
      show ((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
        = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl,
      schurCutoffShiftConj_zero H r B hB hr hL hDA hbdy, schurCutoffShift_zero H r hr hL, sub_zero]
  have hkey := rlctAtOn_comp_homeomorph Θ hΘmp Θ.measurableEmbedding
    (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten q).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1) 0
  rw [hΘ0] at hkey
  rw [← hkey]
  congr 1
  funext q
  rw [bareAbsorb_thetaConj_eq_conjAbsorb H r B hB hr hL hDA q]

/-! ### The LIVE route — the gauge-reg Θ-peel sandwich (LANDED, `L = 2`).

(The DEAD comparability route — `rho_residual_epsBound` / `link2_rho_residual` / `link2_at_zero`,
REFUTED 2026-06-29: `F = ∑R'(Θq)²+C` and `Φ = ∑R'(q)²+C` have DIFFERENT zero sets, exact-rational
witnesses a44dd7e4 — has been REMOVED. It carried a `sorry` for an UNBUILDABLE bound and is fully
superseded by the gauge-reg sandwich below, which closes sorry-free.)

LINK2 (conj→bare core, at `0 : DeepestSplit`,
`regStraighten` reg term) closes by dropping to the GAUGE reg `∑q.1²` — where the BANKED Θ-peel
`rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (@439) converts bare↔conj with NO drag (`Θ` fixes `q.1`) — and
lifting back via the `rlctAtOn_regAbsorb_reduce2` (π̃ option-D) LOCAL-DIFFEO reg-absorb (which preserves zero
sets, so the dead comparability does not recur). The two `hpeel` residuals discharge via
`rlctAtOn_comp_localDiffeo` + the `DeepestL2ConjSmooth` `hTilde` lemmas (the conj one rides the value-fold
atom `deepestEFull_coreConstant`; the bare one is the wire's `hTilde` strict-deriv). `L = 2` (`Fin 3`),
the `deepestEFull_coreConstant` atom's scope. -/

/-- **π̃ reg-absorb peel, CONJ side (LANDED).** The `hpeel` input `rlctAtOn_regAbsorb_reduce2` needs for
`coreAbsorb := conjAbsorb`, `E := deepestEFull`: the conjugated π̃ `q ↦ (deepestEFull (conjAbsorb.symm q),
q.2)` is a local diffeo at `0`. Supplied by `deepestEFull_conj_hTilde_exists` (its invertible strict-deriv
rides the value-fold atom: the conj shift's nonzero `Dδ` moves only the core slot, which `D(deepestEFull)(0)`
annihilates), then `rlctAtOn_comp_localDiffeo` peels it. The conj analogue of the wire's bare `hTilde`. -/
theorem regAbsorbPeel_conj (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, deepestEFull H r hr hL J Pf Qf
            ((deepestCoreAbsorbConj H r B hB hr hL hDA).symm q) i ^ 2)
          + deepestCoreF H r q.2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  set coreAbsorb := deepestCoreAbsorbConj H r B hB hr hL hDA with hca_def
  obtain ⟨eTilde, hTilde_contdiff, hTilde_deriv⟩ :=
    deepestEFull_conj_hTilde_exists H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22
      hPtri hQtri
  have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
    have hca_base : coreAbsorb 0 = 0 := by
      rw [hca_def]; exact deepestCoreAbsorbConj_basepoint H r B hB hr hL hDA hbdy
    conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
  have hkey := rlctAtOn_comp_localDiffeo
    (fun q : DeepestSplit H r (deepestNGauge H r) => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
    (0 : DeepestSplit H r (deepestNGauge H r))
    (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)))
    eTilde hTilde_contdiff hTilde_deriv
    (regStraightenOf2_basepoint (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) (by
      show deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm 0) = 0
      rw [hsymm0]; exact deepestEFull_base H r hr hL (le_refl 2) J Pf Qf))
  have hfun : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).1 i ^ 2)
          + deepestCoreF H r
            (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).2.1)
      = fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) i ^ 2) + deepestCoreF H r q.2.1 := by
    funext q; rfl
  rw [hfun] at hkey
  exact hkey

/-- **π̃ reg-absorb peel, BARE side (LANDED).** The bare analogue of `regAbsorbPeel_conj`
(`coreAbsorb := deepestCoreAbsorb`); the bare π̃'s local-diffeo data is `deepestEFull_bare_hTilde_exists`
(`D(coreAbsorb.symm)(0) = id`, so `eTilde = e` directly). IS the wire's `hTilde` (DeepestL2Wiring:238). -/
theorem regAbsorbPeel_bare (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2)))
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂)) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, deepestEFull H r hr hL J Pf Qf
            ((deepestCoreAbsorb H r hr hL).symm q) i ^ 2)
          + deepestCoreF H r q.2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  set coreAbsorb := deepestCoreAbsorb H r hr hL with hca_def
  obtain ⟨eTilde, hTilde_contdiff, hTilde_deriv⟩ :=
    deepestEFull_bare_hTilde_exists H r hr hL J Pf Qf hPf hQf hQf0 hPfL hQf22
  have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
    have hca_base : coreAbsorb 0 = 0 := by
      rw [hca_def]; exact (deepest_coreAbsorb_exists H r hr hL).1
    conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
  have hkey := rlctAtOn_comp_localDiffeo
    (fun q : DeepestSplit H r (deepestNGauge H r) => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
    (0 : DeepestSplit H r (deepestNGauge H r))
    (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)))
    eTilde hTilde_contdiff hTilde_deriv
    (regStraightenOf2_basepoint (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) (by
      show deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm 0) = 0
      rw [hsymm0]; exact deepestEFull_base H r hr hL (le_refl 2) J Pf Qf))
  have hfun : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).1 i ^ 2)
          + deepestCoreF H r
            (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).2.1)
      = fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) i ^ 2) + deepestCoreF H r q.2.1 := by
    funext q; rfl
  rw [hfun] at hkey
  exact hkey

/-- **The gauge-reg reg-absorb (CONJ), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_conj`.** Straightens
the `deepestEFull` reg output down to the gauge reg `∑q.1²`, holding the CONJ core absorb fixed. -/
theorem regAbsorb_conj (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, deepestEFull H r hr hL J Pf Qf q i ^ 2)
          + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) :=
  rlctAtOn_regAbsorb_reduce2 (deepestCoreAbsorbConj H r B hB hr hL hDA)
    (deepestEFull H r hr hL J Pf Qf) (fun rr => ∑ i, rr i ^ 2) (deepestCoreF H r)
    (deepestCoreAbsorbConj_mp H r B hB hr hL hDA)
    (deepestCoreAbsorbConj_basepoint H r B hB hr hL hDA hbdy)
    (deepestCoreAbsorbConj_regular H r B hB hr hL hDA)
    (regAbsorbPeel_conj H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22 hPtri hQtri)

/-- **The gauge-reg reg-absorb (BARE), via `rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_bare`.** -/
theorem regAbsorb_bare (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2)))
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂)) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, deepestEFull H r hr hL J Pf Qf q i ^ 2)
          + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) :=
  rlctAtOn_regAbsorb_reduce2 (deepestCoreAbsorb H r hr hL)
    (deepestEFull H r hr hL J Pf Qf) (fun rr => ∑ i, rr i ^ 2) (deepestCoreF H r)
    (deepestCoreAbsorb_mp H r hr hL)
    ((deepest_coreAbsorb_exists H r hr hL).1)
    ((deepest_coreAbsorb_exists H r hr hL).2.1)
    (regAbsorbPeel_bare H r hr hL J Pf Qf hPf hQf hQf0 hPfL hQf22)

/-- **LINK-2 at `0` — the LIVE gauge-reg sandwich (LANDED, `L = 2`).** With `regStraighten.1 = deepestEFull`
(`hregval`): `conj-target =[regAbsorb_conj] gauge-reg+conjAbsorb =[Θ-peel @439] gauge-reg+bareAbsorb
=[regAbsorb_bare⁻¹] bare-target`. The two π̃ peels (`regAbsorbPeel_conj`/`_bare`) are LANDED via
`rlctAtOn_comp_localDiffeo` + the `DeepestL2ConjSmooth` `hTilde` lemmas. -/
theorem link2_at_zero_gaugeReg (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q) :
    rlctAtOn
        (fun q : DeepestSplit H r (deepestNGauge H r) =>
          (∑ i, (regStraighten q).1 i ^ 2)
            + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1)
        (0 : DeepestSplit H r (deepestNGauge H r))
      = rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, (regStraighten q).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r)) := by
  -- Rewrite `(regStraighten q).1` to `deepestEFull q` (hregval) under both `rlctAtOn` binders.
  simp only [hregval]
  -- conj-target = gauge-reg+conjAbsorb = gauge-reg+bareAbsorb = bare-target.
  rw [regAbsorb_conj H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22 hPtri hQtri,
    ← rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb H r B hB hr hL hDA hbdy,
    ← regAbsorb_bare H r hr hL J Pf Qf hPf hQf hQf0 hPfL hQf22]

/-- **LINK-2 at flat `wstar`** — the `0`-form `link2_at_zero_gaugeReg` transported along the MP homeomorphism
`split` (`rlctAtOn_comp_homeomorph`, `split wstar = 0`). `rlctAtOn(R'∘split + coreF∘conjAbsorb∘split) wstar
= rlctAtOn(R'∘split + coreF∘bareAbsorb∘split) wstar`. -/
theorem link2_at_wstar_gaugeReg (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit_mp : MeasurePreserving split volume volume)
    (wstar : Fin (flatDim H) → ℝ)
    (hsplit_wstar : split wstar = (0 : DeepestSplit H r (deepestNGauge H r))) :
    rlctAtOn
        (fun x : Fin (flatDim H) → ℝ =>
          (∑ i, (regStraighten (split x)).1 i ^ 2)
            + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA (split x)).2.1)
        wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split x)).2.1)
          wstar := by
  -- Transport the `0`-form LINK2 to flat `wstar` via `rlctAtOn_comp_homeomorph split` (both sides).
  have hconj := rlctAtOn_comp_homeomorph split hsplit_mp split.measurableEmbedding
    (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten q).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.1) wstar
  have hbare := rlctAtOn_comp_homeomorph split hsplit_mp split.measurableEmbedding
    (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (∑ i, (regStraighten q).1 i ^ 2)
        + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1) wstar
  rw [hsplit_wstar] at hconj hbare
  rw [hconj, hbare]
  exact link2_at_zero_gaugeReg H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22
    hPtri hQtri regStraighten hregval

/-- **The L=2 diffeo bridge, ASSEMBLED — the BARE canonical target, sorry-free.** `Φscore = R'∘split +
coreF∘BAREabsorb∘split` at `wstar`, the conclusion of `deepest_diffeo_bridge_L2` / the `hstep2` L=2 branch
consumes. Route: LINK1 (`deepest_diffeo_bridge_L2_conj_impl`, Φscore → conj target) ∘ the flat
`link2_at_wstar_gaugeReg` (conj → bare core). The TRUE conjugated hypotheses (`hsub3reg` conj via
`psiSplitRawL2CoreConj`, `hsub4core` conj) replace the bare `_impl`'s W-a-FALSE ones; `coreAbsorb` stays
BARE (route-b). The controller wires this into `deepest_gauge_construction`'s `hstep2`. -/
theorem deepest_diffeo_bridge_L2_assembled (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin 2) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0)
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit_mp : MeasurePreserving split volume volume)
    (hsub3reg : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      (∑ i, (deepestEFull H r hr hL J Pf Qf
          (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)) i) ^ 2)
        = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2)
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q, (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hsub4core : ∀ᶠ x : (Fin (flatDim H) → ℝ) in
        nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      deepestCoreF H r (deepestCoreAbsorbConj H r B hB hr hL hDA
          (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x))).2.1 = Score x)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (deepestCoreAbsorb H r hr hL (split x)).2.1)
          wstar := by
  -- `split wstar = 0` (the basepoint, from `hsplit` + `hwstar`).
  have hsplit_wstar : split wstar = (0 : DeepestSplit H r (deepestNGauge H r)) := by
    rw [hsplit wstar]
    rw [show wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL) from hwstar]
    exact (deepestSplit_mp_basepoint H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))).2
  -- LINK1: `Φscore = conj target`.
  rw [deepest_diffeo_bridge_L2_conj_impl H r B hB hr hL rfl hDA hY hZ J Pf Qf split hsub3reg
      regStraighten hsplit hregval Score hsub4core Φscore hΦscore wstar hwstar]
  -- LINK2 (flat): conj target = bare target.
  exact link2_at_wstar_gaugeReg H r B hB hr hL hDA hbdy J hJfront Pf Qf hPf hQf hQf0 hPfL hQf22
    hPtri hQtri regStraighten hregval split hsplit_mp wstar hsplit_wstar

end DLNFibre.DLN.RLCT
