import DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderiv
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProductPivot

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderivPivot` — the PIVOT reg-slice product collapse

The reg-slice value-fold for the PIVOT-aware framed product (Stage D, the PIN1 input). Mirrors
`DeepestRegSliceFderiv`'s threshold collapse for `framedParamsRegPivot`: the first `L−1` layers of
`framedParamsRegPivot` are LITERALLY `framedParamsReg` (the prefix is threshold), so the threshold
`firstShapeF` prefix carries over verbatim; only the LAST layer differs (its `.succ` column reindex is
the pivot split). The headline `prod_framedParamsRegPivot_regSlice_collapse` lands the explicit closed
form `firstShapeF (lastLayer).castSucc · (pivot last layer)`, from which `deepestEPivot`'s reg-slice
value is a read of the three residual blocks (the input to the strict-derivative assembly).
-/

open Matrix
open scoped BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The `lastLayer` framed PIVOT reg-slice layer (`L ≥ 2`): `X = Z = 0` (last ≠ first), so it is
`corM_pivot + Pf · reindex(fromBlocks 0 Y 0 0) · Qf` (pivot column split on the `.succ` side). The pivot
analogue of `framedParamsReg_regSlice_last`. -/
theorem framedParamsRegPivot_regSlice_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (r0 : Fin (deepestNReg H r) → ℝ) :
    framedParamsRegPivot H r hr hL J Pf Qf (r0, 0) (lastLayer hL)
      = Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
          (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
        + Pf (lastLayer hL)
          * Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
              (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
              (Matrix.fromBlocks 0 (gaugeReadY H r hr hL (r0, 0) (lastLayer hL)) 0 0)
          * Qf (lastLayer hL) := by
  have hfl : lastLayer hL ≠ firstLayer hL := by
    simp only [firstLayer, lastLayer, ne_eq, Fin.mk.injEq]; omega
  rw [framedParamsRegPivot_last H r hr hL J Pf Qf (r0, 0),
    gaugeReadX_regSlice_zero_of_ne H r hr hL r0 _ hfl, gaugeReadZ_regSlice_zero_of_ne H r hr hL r0 _ hfl]

/-- The reg-slice running product through the first `m` layers of `framedParamsRegPivot` agrees with the
threshold `framedParamsReg` for `m ≤ L−1` (those layers are all NON-last). -/
theorem prodAux_framedParamsRegPivot_regSlice_eq_threshold (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (r0 : Fin (deepestNReg H r) → ℝ)
    (m : ℕ) (hm : m < L + 1) (hmL : m ≤ L - 1) :
    prodAux H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)) m hm
      = prodAux H (framedParamsReg H r hr hL Pf Qf (r0, 0)) m hm := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hm' : m < L + 1 := Nat.lt_of_succ_lt hm
      have hmL1 : m < L := by omega
      have e1 : (⟨m, hm'⟩ : Fin (L + 1)) = (⟨m, hmL1⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨m + 1, hm⟩ : Fin (L + 1)) = (⟨m, hmL1⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      have hne : (⟨m, hmL1⟩ : Fin L) ≠ lastLayer hL := by
        simp only [lastLayer, ne_eq, Fin.mk.injEq]; omega
      have hlayer : framedParamsRegPivot H r hr hL J Pf Qf (r0, 0) ⟨m, hmL1⟩
          = framedParamsReg H r hr hL Pf Qf (r0, 0) ⟨m, hmL1⟩ :=
        framedParamsRegPivot_of_ne_last H r hr hL J Pf Qf (r0, 0) ⟨m, hmL1⟩ hne
      show prodAux H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)) m hm'
          * ((by rw [e1, e2]; exact framedParamsRegPivot H r hr hL J Pf Qf (r0, 0) ⟨m, hmL1⟩ :
            Matrix (Fin (H ⟨m, hm'⟩)) (Fin (H ⟨m + 1, hm⟩)) ℝ))
        = prodAux H (framedParamsReg H r hr hL Pf Qf (r0, 0)) m hm'
          * ((by rw [e1, e2]; exact framedParamsReg H r hr hL Pf Qf (r0, 0) ⟨m, hmL1⟩ :
            Matrix (Fin (H ⟨m, hm'⟩)) (Fin (H ⟨m + 1, hm⟩)) ℝ))
      rw [ih hm' (by omega)]
      refine congrArg (prodAux H (framedParamsReg H r hr hL Pf Qf (r0, 0)) m hm' * ·) ?_
      cases e1; cases e2; rw [hlayer]

/-- **The pivot reg-slice product collapse** (`L ≥ 2`, `Qf firstLayer = 1`): the framed PIVOT product
`prod (framedParamsRegPivot (r0,0))` is `firstShapeF (lastLayer).castSucc · (pivot last layer)` — the
running product through the first `L−1` layers is the threshold `firstShapeF` (those layers are all
threshold), and the final fold multiplies by the pivot last layer (the only one with a nonzero Y
deviation, pivot column split). The pivot analogue of `prod_regSlice_collapse`. -/
theorem prod_framedParamsRegPivot_regSlice_collapse {n : ℕ} (H : Fin (n + 1 + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (n + 1 + 1), r ≤ H s) (hL : 1 ≤ n + 1) (hL2 : 2 ≤ n + 1)
    (J : Fin r ↪ Fin (H (Fin.last (n + 1))))
    (Pf : (s : Fin (n + 1)) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin (n + 1)) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hQf0 : Qf (firstLayer hL) = 1) (r0 : Fin (deepestNReg H r) → ℝ) :
    prod H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0))
      = firstShapeF H r hr hL Pf Qf r0 (lastLayer hL).castSucc
          * framedParamsRegPivot H r hr hL J Pf Qf (r0, 0) (lastLayer hL) := by
  -- `prod = prodAux (n+1)`; unfold the last fold via `prodAux_succ`; the prefix `prodAux n` collapses
  -- to the threshold `firstShapeF` (prefix layers are threshold), and the last layer is the pivot one.
  have e1H : H (⟨n, Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1 + 1))
      = H ((⟨n, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1)).castSucc) := rfl
  have e2H : H (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 1 + 1))
      = H ((⟨n, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1)).succ) := rfl
  show prodAux H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)) (n + 1) (Nat.lt_succ_self (n + 1)) = _
  rw [prodAux_succ H (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)) n (Nat.lt_succ_self (n + 1))
      e1H e2H]
  -- the recast last layer = `framedParamsRegPivot lastLayer` (finCongr identity casts; `⟨n,_⟩ = lastLayer`).
  have hinner : Matrix.reindex (finCongr e1H.symm) (finCongr e2H.symm)
        (framedParamsRegPivot H r hr hL J Pf Qf (r0, 0)
          (⟨n, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1)))
      = framedParamsRegPivot H r hr hL J Pf Qf (r0, 0) (lastLayer hL) := by
    apply Matrix.ext; intro i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply]
    rfl
  rw [hinner]
  -- the prefix `prodAux n` equals the threshold prefix, which collapses to `firstShapeF ⟨n,_⟩`.
  rw [prodAux_framedParamsRegPivot_regSlice_eq_threshold H r hr hL J Pf Qf r0 n
      (Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))) (by omega)]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · omega  -- n = 0 ⟹ L = 1, contradicts `2 ≤ L`.
  · rw [prodAux_regSlice_through_first H r hr hL hL2 Pf Qf hQf0 r0 n
        (Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))) hnpos (by omega)]
    rfl

end DLNFibre.DLN.RLCT
