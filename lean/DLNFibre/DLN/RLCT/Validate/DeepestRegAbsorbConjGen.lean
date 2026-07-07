import DLNFibre.DLN.RLCT.Validate.DeepestL2ConjSmooth

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbConjGen` — the general-`L` CONJUGATE reg-absorb (Step Θ piece 1)

The general-`L` lift of the `Fin 3` conjugate reg-absorb chain (`DeepestL2ConjSub4`'s `regAbsorb_conj`,
riding the `Fin 3` value-fold atom `deepestEFull_coreConstant`). This is the ONE Step-Θ geometry piece
deferred by `DeepestDiffeoBridgeGenTheta` (threaded there as `hRegAbsorbConj`); landing it makes
`link2_at_wstar_gaugeReg_gen` UNCONDITIONAL.

## The crux — the general corner factorization
The `Fin 3` atom `deepestEFull_coreConstant` used the two-layer unfold `prodDecode_eq_two_of_L2`. The
general lift replaces it with a `prodAux` prefix induction (mirroring `prodAux_framedParamsReg_zero_aux`):
at the reg=spec=0 slice EACH framed layer reindexes to the block-corner `fromBlocks 1 0 0 (T_s)`
(`reindex_framedLayer_zeroReads_eq_corner`, given the per-layer triangularity `hPtri`/`hQtri` — dischargeable
at the wire since strict-interior frames are the identity, `deepestPoint_frame_pivot_triangular_exists`'s
`hInterior`), and the corner-block product telescopes `∏ fromBlocks 1 0 0 T_s = fromBlocks 1 0 0 (∏ T_s)`
(`fromBlocks_one_corner_mul` folded along `reindex_mul_split`). So the reindexed framed product's
`{11,12,21}` blocks are the core-INDEPENDENT corner `(1,0,0)`, whence `deepestEFull(0,c,0) = deepestEFull(0,0,0)`.

## The conj chain (mirror of `DeepestL2ConjSub4`)
`deepestEFull_coreConstant_gen` → `deepestEFull_coreInBlock_zero_gen` (`D_E ∘ coreInCLM = 0`) →
`deepestEFull_conj_hTilde_exists_gen` (the conj π̃ is a local diffeo at `0`: the conj shift's nonzero
`Dδ` moves only the core slot, which `D_E` annihilates) → `regAbsorbPeel_conj_gen` → `regAbsorb_conj_gen`.
Every support lemma (`contDiff_schurCutoffShiftConj`, `deepestEPivot_regSlice_fderiv`,
`regStraightenTotalCLM2_equiv_of_regBlock_isUnit`, …) is already general.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The reindexed identity is the block corner** `fromBlocks 1 0 0 1` (the prefix-induction base). -/
theorem reindex_one_eq_fromBlocks_one {n r m : ℕ} (e : Fin n ≃ Fin r ⊕ Fin m) :
    Matrix.reindex e e (1 : Matrix (Fin n) (Fin n) ℝ)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 (1 : Matrix (Fin m) (Fin m) ℝ) := by
  have h1 : Matrix.reindex e e (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Equiv.apply_eq_iff_eq]
  rw [h1, Matrix.fromBlocks_one]

/-- **The per-layer corner at the reg=spec=0 slice** (∀ `s : Fin L`). Each framed layer reindexes (via the
threshold split on both sides) to the block-corner `fromBlocks 1 0 0 (junk_s)`. Non-last layers are
`framedLayer` (`framedParamsPivot_zeroReg_of_ne`); the last layer's pivot column split collapses to the
threshold split (`hJfront` ⟹ `pivotThresholdSplit_pivotJSucc_frontEmbed`); both close by
`reindex_framedLayer_zeroReads_eq_corner` (the block-lower `hPtri`/block-upper `hQtri` triangularity). -/
theorem framedParamsPivot_zeroReg_reindex_corner (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (c : Fin (flatDim (deepestM H r)) → ℝ) (s : Fin L) :
    ∃ T : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ,
      Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
          (rThresholdSplit r (H s.succ) (hr s.succ))
          (framedParamsPivot H r hr hL J Pf Qf
            ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) s)
        = Matrix.fromBlocks 1 0 0 T := by
  by_cases hs : s = lastLayer hL
  · subst hs
    have hbridge : framedParamsPivot H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) (lastLayer hL)
        = framedLayer H r hr (lastLayer hL) (Pf (lastLayer hL)) (Qf (lastLayer hL)) 0 0 0
            ((paramsEquivFlat (deepestM H r)).symm c (lastLayer hL)) := by
      rw [framedParamsPivot_zeroReg_last H r hr hL J Pf Qf c, hJfront,
        pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL]
      rfl
    rw [hbridge]
    exact ⟨_, reindex_framedLayer_zeroReads_eq_corner H r hr (lastLayer hL) (Pf (lastLayer hL))
      (Qf (lastLayer hL)) _ (hPtri (lastLayer hL)) (hQtri (lastLayer hL))⟩
  · rw [framedParamsPivot_zeroReg_of_ne H r hr hL J Pf Qf c s hs]
    exact ⟨_, reindex_framedLayer_zeroReads_eq_corner H r hr s (Pf s) (Qf s) _
      (hPtri s) (hQtri s)⟩

/-- **The prefix corner-telescoping** (∀ `k`). The running product through the first `k` framed layers at
the reg=spec=0 slice reindexes to the block-corner `fromBlocks 1 0 0 (junk_k)`. Base `k = 0` is the
reindexed identity (`reindex_one_eq_fromBlocks_one`); the step folds the per-layer corner
(`framedParamsPivot_zeroReg_reindex_corner`) onto the prefix via `reindex_mul_split` +
`fromBlocks_one_corner_mul`. Mirrors `prodAux_framedParamsReg_zero_aux`, with core-`c` corners. -/
theorem prodAux_framedParamsPivot_zeroReg_corner (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (c : Fin (flatDim (deepestM H r)) → ℝ) :
    ∀ (k : ℕ) (hk : k < L + 1),
      ∃ T : Matrix (Fin (H 0 - r)) (Fin (H ⟨k, hk⟩ - r)) ℝ,
        Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (rThresholdSplit r (H ⟨k, hk⟩) (hr ⟨k, hk⟩))
            (prodAux H (framedParamsPivot H r hr hL J Pf Qf
              ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))) k hk)
          = Matrix.fromBlocks 1 0 0 T := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact ⟨(1 : Matrix (Fin (H 0 - r)) (Fin (H 0 - r)) ℝ),
        reindex_one_eq_fromBlocks_one (rThresholdSplit r (H 0) (hr 0))⟩
  | succ k ih =>
      intro hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have e1 : H (⟨k, hk'⟩ : Fin (L + 1)) = H ((⟨k, hkL⟩ : Fin L).castSucc) := rfl
      have e2 : H (⟨k + 1, hk⟩ : Fin (L + 1)) = H ((⟨k, hkL⟩ : Fin L).succ) := rfl
      obtain ⟨Tp, hTp⟩ := ih hk'
      obtain ⟨Tk, hTk⟩ := framedParamsPivot_zeroReg_reindex_corner H r hr hL J hJfront Pf Qf
        hPtri hQtri c ⟨k, hkL⟩
      -- Collapse the `prodAux` succ-cast (`finCongr rfl = id`), giving the plain layer at running widths.
      have hrecast : Matrix.reindex (rThresholdSplit r (H (⟨k, hk'⟩ : Fin (L + 1)))
              (hr (⟨k, hk'⟩ : Fin (L + 1))))
            (rThresholdSplit r (H (⟨k + 1, hk⟩ : Fin (L + 1))) (hr (⟨k + 1, hk⟩ : Fin (L + 1))))
            (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
              (framedParamsPivot H r hr hL J Pf Qf
                ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))
                (⟨k, hkL⟩ : Fin L)))
          = Matrix.fromBlocks 1 0 0 Tk := by
        have hcollapse : Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
              (framedParamsPivot H r hr hL J Pf Qf
                ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))
                (⟨k, hkL⟩ : Fin L))
            = framedParamsPivot H r hr hL J Pf Qf
                ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))
                (⟨k, hkL⟩ : Fin L) := by
          apply Matrix.ext; intro i j
          simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply]
          rfl
        rw [hcollapse]; exact hTk
      rw [prodAux_succ H (framedParamsPivot H r hr hL J Pf Qf
            ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))) k hk e1 e2,
        reindex_mul_split (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (⟨k, hk'⟩ : Fin (L + 1))) (hr (⟨k, hk'⟩ : Fin (L + 1))))
          (rThresholdSplit r (H (⟨k + 1, hk⟩ : Fin (L + 1))) (hr (⟨k + 1, hk⟩ : Fin (L + 1)))),
        hTp, hrecast]
      exact ⟨_, fromBlocks_one_corner_mul Tp Tk⟩

/-- **The general framed corner** — the reindexed framed product at the reg=spec=0 slice is the
core-INDEPENDENT block corner `fromBlocks 1 0 0 (junk)`. Specialize the prefix telescoping at `k = L`
(the `⟨L,_⟩ = Fin.last L` index aligns), collapse the outer pivot column split to the threshold split
(`hJfront`). The general lift of `prod_framedParamsPivot_zeroReg_eq_corner` (`Fin 3`). -/
theorem prod_framedParamsPivot_zeroReg_eq_corner_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (c : Fin (flatDim (deepestM H r)) → ℝ) :
    ∃ junk : Matrix (Fin (H 0 - r)) (Fin (H (Fin.last L) - r)) ℝ,
      Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf
            ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))))
        = Matrix.fromBlocks 1 0 0 junk := by
  have hpivOuter : pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J
      = rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) := by
    rw [hJfront]; exact pivotThresholdSplit_frontEmbed H r hr
  rw [hpivOuter]
  obtain ⟨junk, hjunk⟩ := prodAux_framedParamsPivot_zeroReg_corner H r hr hL J hJfront Pf Qf
    hPtri hQtri c L (Nat.lt_succ_self L)
  exact ⟨junk, hjunk⟩

/-- **The value-fold atom, general `L`** — at the regular-and-spectator-zero slice, `deepestEFull` is
INDEPENDENT of the core slot: `deepestEFull(0,c,0) = deepestEFull(0,0,0)`. Both reindexed framed products
are `fromBlocks 1 0 0 (junk)` (`prod_framedParamsPivot_zeroReg_eq_corner_gen`), so their `{11,12,21}`
blocks are the core-independent corner `(1,0,0)`; `deepestEFull_eq_of_framedProd_regBlocks_eq` concludes. -/
theorem deepestEFull_coreConstant_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (c : Fin (flatDim (deepestM H r)) → ℝ) :
    deepestEFull H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))
      = deepestEFull H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ),
          (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ)) := by
  obtain ⟨junkc, hjunkc⟩ :=
    prod_framedParamsPivot_zeroReg_eq_corner_gen H r hr hL J hJfront Pf Qf hPtri hQtri c
  obtain ⟨junk0, hjunk0⟩ :=
    prod_framedParamsPivot_zeroReg_eq_corner_gen H r hr hL J hJfront Pf Qf hPtri hQtri 0
  refine deepestEFull_eq_of_framedProd_regBlocks_eq H r hr hL J Pf Qf _ _ ?_ ?_ ?_
  · rw [hjunkc, hjunk0, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₁]
  · rw [hjunkc, hjunk0, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₁₂]
  · rw [hjunkc, hjunk0, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₁]

/-- **`D(deepestEFull)(0)` annihilates the core direction, general `L`** — the value-fold atom
`deepestEFull_coreConstant_gen` makes `c ↦ deepestEFull (0, c, 0)` constant, so its fderiv at `0` is `0`;
that fderiv IS `(fderiv deepestEFull 0).comp coreInCLM` (chain rule). Mirror of
`deepestEFull_coreInBlock_zero` (`Fin 3`). -/
theorem deepestEFull_coreInBlock_zero_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0) :
    (fderiv ℝ (deepestEFull H r hr hL J Pf Qf) 0).comp (coreInCLM H r)
      = (0 : (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) := by
  have hconst : (fun c : Fin (flatDim (deepestM H r)) → ℝ =>
        deepestEFull H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)))
      = fun _ => deepestEFull H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ),
            (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ)) := by
    funext c
    exact deepestEFull_coreConstant_gen H r hr hL J hJfront Pf Qf hPtri hQtri c
  have hgderiv0 : fderiv ℝ (fun c : Fin (flatDim (deepestM H r)) → ℝ =>
        deepestEFull H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))) 0
      = 0 := by
    rw [hconst]
    exact (hasFDerivAt_const _ (0 : Fin (flatDim (deepestM H r)) → ℝ)).fderiv
  set D_E := fderiv ℝ (deepestEFull H r hr hL J Pf Qf) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E 0 :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).hasStrictFDerivAt (by simp)
  have hcoreIn : HasStrictFDerivAt (fun c : Fin (flatDim (deepestM H r)) → ℝ =>
      ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)))
      (coreInCLM H r) 0 := by
    have := (coreInCLM H r).hasStrictFDerivAt (x := (0 : Fin (flatDim (deepestM H r)) → ℝ))
    simpa [coreInCLM] using this
  have hsd0 : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E
      ((0 : Fin (deepestNReg H r) → ℝ),
        (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ)) := hsd
  have hchain := hsd0.comp (x := (0 : Fin (flatDim (deepestM H r)) → ℝ)) hcoreIn
  have := hchain.hasFDerivAt.fderiv
  rw [this] at hgderiv0
  exact hgderiv0

/-- **The conjugated `hTilde`, general `L`** — the conjugated reg-absorb peel's local-diffeo data. The
conjugated straightening `regStraightenOf2 (deepestEFull ∘ deepestCoreAbsorbConj.symm)` is `ContDiff ⊤`
with an INVERTIBLE strict derivative at `0`: the conj shift's nonzero `Dδ` moves only the core slot, which
`D(deepestEFull)(0)` annihilates (`deepestEFull_coreInBlock_zero_gen`), so the reg-block stays the PIN-1
frame `F`. Mirror of `deepestEFull_conj_hTilde_exists` (`Fin 3`). -/
theorem deepestEFull_conj_hTilde_exists_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0) :
    ∃ eTilde : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r),
      ContDiff ℝ (⊤ : ℕ∞)
        (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf
          ((deepestCoreAbsorbConj H r B hB hr hL hDA).symm q))) ∧
      HasStrictFDerivAt (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf
          ((deepestCoreAbsorbConj H r B hB hr hL hDA).symm q)))
        (eTilde : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
          DeepestSplit H r (deepestNGauge H r)) 0 := by
  set coreAbsorb := deepestCoreAbsorbConj H r B hB hr hL hDA with hca_def
  set D_E := fderiv ℝ (deepestEFull H r hr hL J Pf Qf) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E 0 :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).hasStrictFDerivAt (by simp)
  obtain ⟨F, hF⟩ := deepestEPivot_regSlice_fderiv H r hr hL hL2 J Pf Qf hPf hQf hQf0 hPfL hQf22
  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      ((r0, 0) : DeepestSplit H r (deepestNGauge H r)))
      (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0 := by
    have := (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      DeepestSplit H r (deepestNGauge H r)).hasStrictFDerivAt (x := 0)
    simpa [regInCLM] using this
  have hregslice : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEFull H r hr hL J Pf Qf (r0, 0))
      (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 := by
    have hbridge : (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEFull H r hr hL J Pf Qf (r0, 0))
        = fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL J Pf Qf (r0, 0) := by
      funext r0; exact deepestEFull_coreZero H r hr hL J Pf Qf r0 0
    rw [hbridge]; exact hF
  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEFull H r hr hL J Pf Qf (r0, 0)) (D_E.comp regInCLM) 0 :=
    hsd.comp (x := (0 : Fin (deepestNReg H r) → ℝ)) hregIn
  have hblock : (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ))
      = D_E.comp (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
        DeepestSplit H r (deepestNGauge H r)) := by
    have h1 := hcomp.hasFDerivAt.fderiv
    have h2 := hregslice.hasFDerivAt.fderiv
    rw [← h1, ← h2]
  have hcoreZero : D_E.comp (coreInCLM H r)
      = (0 : (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) :=
    deepestEFull_coreInBlock_zero_gen H r hr hL J hJfront Pf Qf hPtri hQtri
  have hcds : ContDiff ℝ (⊤ : ℕ∞) (schurCutoffShiftConj H r B hB hr hL hDA) :=
    contDiff_schurCutoffShiftConj H r B hB hr hL hDA
  set Dδ := fderiv ℝ (schurCutoffShiftConj H r B hB hr hL hDA) 0 with hDδ
  have hshift_sd : HasStrictFDerivAt (schurCutoffShiftConj H r B hB hr hL hDA) Dδ 0 :=
    hcds.hasStrictFDerivAt (by simp)
  have hsymm_cd : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q) := by
    rw [hca_def, deepestCoreAbsorbConj]
    exact contDiff_coreShearHomeo_symm (schurCutoffShiftConj H r B hB hr hL hDA)
      (continuous_schurCutoffShiftConj H r B hB hr hL hDA) hcds
  have hsymm_sd : HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q)
      (coreShearSymmCLM Dδ) 0 := by
    rw [hca_def, deepestCoreAbsorbConj]
    exact hasStrictFDerivAt_coreShearHomeo_symm_gen (schurCutoffShiftConj H r B hB hr hL hDA)
      (continuous_schurCutoffShiftConj H r B hB hr hL hDA) Dδ hshift_sd
  set Ecomp : DeepestSplit H r (deepestNGauge H r) → (Fin (deepestNReg H r) → ℝ) :=
    fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) with hEcomp
  have hEcomp_cd : ContDiff ℝ (⊤ : ℕ∞) Ecomp :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).comp hsymm_cd
  have hcontdiff : ContDiff ℝ (⊤ : ℕ∞) (regStraightenOf2 Ecomp) :=
    contDiff_regStraightenOf2 Ecomp hEcomp_cd
  have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
    have hca_base : coreAbsorb 0 = 0 := by
      rw [hca_def]
      exact deepestCoreAbsorbConj_basepoint H r B hB hr hL hDA hbdy
    conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
  have hEcomp_sd : HasStrictFDerivAt Ecomp (D_E.comp (coreShearSymmCLM Dδ)) 0 := by
    have hsd' : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E
        (coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r))) := by
      rw [hsymm0]; exact hsd
    exact hsd'.comp (x := (0 : DeepestSplit H r (deepestNGauge H r))) hsymm_sd
  have hreg_sd := hasStrictFDerivAt_regStraightenOf2_gen Ecomp (D_E.comp (coreShearSymmCLM Dδ)) hEcomp_sd
  have hregblock : (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ))
      = (D_E.comp (coreShearSymmCLM Dδ)).comp
        (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) := by
    refine ContinuousLinearMap.ext (fun r0 => ?_)
    rw [hblock]
    simp only [ContinuousLinearMap.comp_apply, regInCLM_apply, coreShearSymmCLM_apply]
    show D_E ((r0 : Fin (deepestNReg H r) → ℝ),
        (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
      = D_E ((r0, (0 : Fin (flatDim (deepestM H r)) → ℝ)
          - Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ)), (0 : Fin (deepestNGauge H r) → ℝ)))
    rw [show ((r0 : Fin (deepestNReg H r) → ℝ),
          (0 : Fin (flatDim (deepestM H r)) → ℝ) - Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ)),
          (0 : Fin (deepestNGauge H r) → ℝ))
        = ((r0, (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
            : DeepestSplit H r (deepestNGauge H r))
          + coreInCLM H r (- Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ))) from by
      simp only [coreInCLM_apply, Prod.mk_add_mk, add_zero, zero_add, zero_sub]]
    rw [map_add]
    have : D_E (coreInCLM H r (- Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ)))) = 0 := by
      have := ContinuousLinearMap.ext_iff.1 hcoreZero (- Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ)))
      simpa using this
    rw [this, add_zero]
  obtain ⟨e, he⟩ := regStraightenTotalCLM2_equiv_of_regBlock_isUnit
    (W := (Fin (flatDim (deepestM H r)) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (D_E.comp (coreShearSymmCLM Dδ)) F hregblock
  refine ⟨e, hcontdiff, ?_⟩
  rw [he]
  exact hreg_sd

/-- **π̃ reg-absorb peel, CONJ side, general `L`** (mirror of `regAbsorbPeel_conj`). The conjugated π̃ is a
local diffeo at `0` (`deepestEFull_conj_hTilde_exists_gen`); `rlctAtOn_comp_localDiffeo` peels it. -/
theorem regAbsorbPeel_conj_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
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
    deepestEFull_conj_hTilde_exists_gen H r B hB hr hL hL2 hDA hbdy J hJfront Pf Qf
      hPf hQf hQf0 hPfL hQf22 hPtri hQtri
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
      rw [hsymm0]; exact deepestEFull_base H r hr hL hL2 J Pf Qf))
  have hfun : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).1 i ^ 2)
          + deepestCoreF H r
            (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q)) q).2.1)
      = fun q : DeepestSplit H r (deepestNGauge H r) =>
        (∑ i, deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) i ^ 2) + deepestCoreF H r q.2.1 := by
    funext q; rfl
  rw [hfun] at hkey
  exact hkey

/-- **The gauge-reg reg-absorb (CONJ), general `L`** (mirror of `regAbsorb_conj`), via
`rlctAtOn_regAbsorb_reduce2` + `regAbsorbPeel_conj_gen`: straightens the `deepestEFull` reg output down to
the gauge reg `∑ q.1²`, holding the CONJ core absorb fixed. **This discharges the Step-Θ `hRegAbsorbConj`.** -/
theorem regAbsorb_conj_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin L, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
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
    (regAbsorbPeel_conj_gen H r B hB hr hL hL2 hDA hbdy J hJfront Pf Qf
      hPf hQf hQf0 hPfL hQf22 hPtri hQtri)

end DLNFibre.DLN.RLCT
