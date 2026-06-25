import DLNFibre.DLN.RLCT.Validate.DeepestTelescoping

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedProductPivot` — the PIVOT-aware framed product (Stage C)

The L2-PIN1 consumer migration needs `deepestEPivot`'s LAST-layer `.succ`-side column split to align
with `B`'s pivot columns (`pivotThresholdSplit r (H (Fin.last L)) J`), so the `P12` residual derivative
block reads `Y · (reindex eJ eJ Q)₂₂` with the pivot-aligned `B22` block the frame fact certifies a
unit. The blocker (Codex-verified, prior tide): `framedLayer` (`DeepestFramedProduct`) hardcodes
`rThresholdSplit` on the `.succ` column side, so the THRESHOLD origin product `prodAux_framedParamsReg_zero`
lands the threshold corner frame-independently. Migrating `deepestEPivot`'s last-layer column split to
`pivotThresholdSplit J` while the origin product still lands the threshold corner makes the base fact
(`deepestEPivot 0 = 0`) FALSE for non-front pivots. So the origin product must be made PIVOT-aware FIRST.

This module is that **additive** Stage-C bedrock (no mutation of `framedLayer` or its existing
consumers): a pivot-aware last-layer framed reconstruction `framedParamsRegPivot` whose LAST-layer
`.succ`-side reindex uses `pivotThresholdSplit r (H (Fin.last L)) J` (first/interior layers KEEP
`rThresholdSplit`), plus the pivot origin-product lemma `prodAux_framedParamsRegPivot_zero`: at the
origin, the product lands the PIVOT corner (threshold-ROW / pivot-COLUMN). It REUSES the threshold prefix
product `prodAux_framedParamsReg_zero_aux` (the first `L−1` layers are literally `framedParamsReg`) and
folds only the last layer specially with `corner_reindex_mul` (generic over the right output split).

The pivot embedding `J` is supplied on `Fin (H (Fin.last L))` (the type `prod`'s columns live in, and
the type `deepestEPivot`'s outer reindex consumes); the last layer's `.succ` width `H ((lastLayer hL).succ)`
equals it only up to `H_lastLayer_succ` (a `congr`, NOT defeq), so `J` is transported into the last-layer
`.succ` width by `finCongr (H_lastLayer_succ H hL).symm`. The single `finCongr` cast bridge lives here.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The pivot embedding transported from `Fin (H (Fin.last L))` (where `deepestEPivot`'s outer reindex
lives) into the last layer's `.succ` width `Fin (H ((lastLayer hL).succ))` (where `framedLayer`'s
`.succ`-side reindex lives), via `finCongr (H_lastLayer_succ H hL).symm`. -/
noncomputable def pivotJSucc (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) : Fin r ↪ Fin (H ((lastLayer hL).succ)) :=
  J.trans (finCongr (H_lastLayer_succ H hL).symm).toEmbedding

/-- **The pivot-aware framed reconstruction** (`framedParamsRegPivot`). Identical to `framedParamsReg`
on every NON-last layer (so the threshold telescoping / reg-slice lemmas apply there verbatim); on the
LAST layer the `.succ`-side column reindex uses `pivotThresholdSplit r (H last.succ) (pivotJSucc J)`
instead of `rThresholdSplit r (H last.succ)`. The `T = 0` core reconstruction (`deepestEPivot`'s
reconstruction half), pivot-aligned at the last interface. -/
noncomputable def framedParamsRegPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) : Params H :=
  fun s =>
    if hs : s = lastLayer hL then
      -- last layer: pivot column split on the `.succ` side
      (by
        rw [hs]
        exact
          Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
              (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
              (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
            + P (lastLayer hL)
              * Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
                  (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
                  (Matrix.fromBlocks (readX H r hr hL p (lastLayer hL))
                    (readY H r hr hL p (lastLayer hL)) (readZ H r hr hL p (lastLayer hL)) 0)
              * Q (lastLayer hL) :
          Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ)
    else
      framedParamsReg H r hr hL P Q p s

/-- On every NON-last layer, `framedParamsRegPivot` is `framedParamsReg` (the threshold path). -/
theorem framedParamsRegPivot_of_ne_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (s : Fin L) (hs : s ≠ lastLayer hL) :
    framedParamsRegPivot H r hr hL J P Q p s = framedParamsReg H r hr hL P Q p s := by
  simp only [framedParamsRegPivot, dif_neg hs]

/-- The LAST layer of `framedParamsRegPivot` (the pivot-spelled formula). -/
theorem framedParamsRegPivot_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) :
    framedParamsRegPivot H r hr hL J P Q p (lastLayer hL)
      = Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
            (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
          + P (lastLayer hL)
            * Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
                (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
                (Matrix.fromBlocks (readX H r hr hL p (lastLayer hL))
                  (readY H r hr hL p (lastLayer hL)) (readZ H r hr hL p (lastLayer hL)) 0)
            * Q (lastLayer hL) := by
  show (dite (lastLayer hL = lastLayer hL) _ _) = _
  rw [dif_pos rfl]
  rfl

/-- Each `framedParamsRegPivot` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: non-last layers
ARE `framedParamsReg` (the banked `contDiff_framedParamsReg_entry`); the last layer is the same
`corM + P·reindex(fromBlocks readX readY readZ 0)·Q` block-read shape with a pivot column reindex
(`ContDiff` by the same double-sum-of-reads argument, generic over the reindex equiv). -/
theorem contDiff_framedParamsRegPivot_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (s : Fin L)
    (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsRegPivot H r hr hL J P Q p s i j) := by
  by_cases hs : s = lastLayer hL
  · -- last layer: pivot column reindex. The entry is `corM_pivot i j + (P·D(p)·Q) i j` with each entry
    -- of `D(p) = reindex(fromBlocks (readX) (readY) (readZ) 0)` a block read (ContDiff) or `0`.
    subst hs
    have hD : ∀ (m : Fin (H (lastLayer hL).castSucc)) (n : Fin (H (lastLayer hL).succ)),
        ContDiff ℝ (⊤ : ℕ∞) (fun p => (Matrix.reindex
            (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
            (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
            (Matrix.fromBlocks (readX H r hr hL p (lastLayer hL)) (readY H r hr hL p (lastLayer hL))
              (readZ H r hr hL p (lastLayer hL))
              (0 : Matrix (Fin (H (lastLayer hL).castSucc - r)) (Fin (H (lastLayer hL).succ - r)) ℝ)))
            m n) := by
      intro m n
      have hmn : (fun p => (Matrix.reindex
            (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
            (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
            (Matrix.fromBlocks (readX H r hr hL p (lastLayer hL)) (readY H r hr hL p (lastLayer hL))
              (readZ H r hr hL p (lastLayer hL))
              (0 : Matrix (Fin (H (lastLayer hL).castSucc - r)) (Fin (H (lastLayer hL).succ - r)) ℝ)))
            m n)
          = fun p => Matrix.fromBlocks (readX H r hr hL p (lastLayer hL))
              (readY H r hr hL p (lastLayer hL)) (readZ H r hr hL p (lastLayer hL))
              (0 : Matrix (Fin (H (lastLayer hL).castSucc - r)) (Fin (H (lastLayer hL).succ - r)) ℝ)
              ((rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)) m)
              ((pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)) n) := by
        funext p
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      rw [hmn]
      rcases (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)) m with a | a <;>
        rcases (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)) n
          with b | b <;>
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
          Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      · exact contDiff_readX_entry H r hr hL (lastLayer hL) a b
      · exact contDiff_readY_entry H r hr hL (lastLayer hL) a b
      · exact contDiff_readZ_entry H r hr hL (lastLayer hL) a b
      · exact contDiff_const
    have hentry : (fun p => framedParamsRegPivot H r hr hL J P Q p (lastLayer hL) i j)
        = fun p =>
            (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
                (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
                (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)) i j
            + (P (lastLayer hL) * Matrix.reindex
                  (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
                  (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
                  (Matrix.fromBlocks (readX H r hr hL p (lastLayer hL))
                    (readY H r hr hL p (lastLayer hL)) (readZ H r hr hL p (lastLayer hL))
                    (0 : Matrix (Fin (H (lastLayer hL).castSucc - r))
                      (Fin (H (lastLayer hL).succ - r)) ℝ)) * Q (lastLayer hL)) i j := by
      funext p
      rw [framedParamsRegPivot_last H r hr hL J P Q p]
      simp only [Matrix.add_apply]
    rw [hentry]
    refine contDiff_const.add ?_
    simp only [Matrix.mul_apply]
    refine ContDiff.sum (fun n _ => ?_)
    refine ContDiff.mul (ContDiff.sum (fun m _ => ?_)) contDiff_const
    exact contDiff_const.mul (hD m n)
  · -- non-last layer: `framedParamsRegPivot = framedParamsReg`, the banked entry continuity.
    have he : (fun p => framedParamsRegPivot H r hr hL J P Q p s i j)
        = fun p => framedParamsReg H r hr hL P Q p s i j := by
      funext p; rw [framedParamsRegPivot_of_ne_last H r hr hL J P Q p s hs]
    rw [he]
    exact contDiff_framedParamsReg_entry H r hr hL P Q s i j

/-- The LAST layer of `framedParamsRegPivot` at the ORIGIN is the threshold-ROW / pivot-COLUMN corner
(the deviation `fromBlocks 0 0 0 0 = 0` vanishes, so the frame term `P · reindex 0 · Q = 0`). -/
theorem framedParamsRegPivot_zero_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    framedParamsRegPivot H r hr hL J P Q 0 (lastLayer hL)
      = Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
          (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  rw [framedParamsRegPivot_last H r hr hL J P Q 0, readX_zero H r hr hL (lastLayer hL),
    readY_zero H r hr hL (lastLayer hL), readZ_zero H r hr hL (lastLayer hL)]
  rw [show Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 = 0 from by
      ext a b; rcases a with a | a <;> rcases b with b | b <;> rfl]
  simp [Matrix.reindex_apply, Matrix.submatrix_zero]

/-- The running product through the first `m` layers of `framedParamsRegPivot` agrees with the threshold
`framedParamsReg` for `m ≤ L−1` (those layers are all NON-last). -/
theorem prodAux_framedParamsRegPivot_eq_threshold_prefix (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (m : ℕ) (hm : m < L + 1) (hmL : m ≤ L - 1) :
    prodAux H (framedParamsRegPivot H r hr hL J P Q 0) m hm
      = prodAux H (framedParamsReg H r hr hL P Q 0) m hm := by
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
      have hlayer : framedParamsRegPivot H r hr hL J P Q 0 ⟨m, hmL1⟩
          = framedParamsReg H r hr hL P Q 0 ⟨m, hmL1⟩ :=
        framedParamsRegPivot_of_ne_last H r hr hL J P Q 0 ⟨m, hmL1⟩ hne
      show prodAux H (framedParamsRegPivot H r hr hL J P Q 0) m hm'
          * ((by rw [e1, e2]; exact framedParamsRegPivot H r hr hL J P Q 0 ⟨m, hmL1⟩ :
            Matrix (Fin (H ⟨m, hm'⟩)) (Fin (H ⟨m + 1, hm⟩)) ℝ))
        = prodAux H (framedParamsReg H r hr hL P Q 0) m hm'
          * ((by rw [e1, e2]; exact framedParamsReg H r hr hL P Q 0 ⟨m, hmL1⟩ :
            Matrix (Fin (H ⟨m, hm'⟩)) (Fin (H ⟨m + 1, hm⟩)) ℝ))
      rw [ih hm' (by omega)]
      refine congrArg (prodAux H (framedParamsReg H r hr hL P Q 0) m hm' * ·) ?_
      cases e1; cases e2; rw [hlayer]

/-- **The pivot prefix product** (`1 ≤ k ≤ L−1`): the running product through the first `k` layers of
`framedParamsRegPivot` at the origin is the THRESHOLD corner — those layers are all NON-last, so they
are literally `framedParamsReg`, and the threshold fold `prodAux_framedParamsReg_zero_aux` applies. -/
theorem prodAux_framedParamsRegPivot_zero_prefix (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (k : ℕ) (hk : k < L + 1) (hk1 : 1 ≤ k) (hkL : k ≤ L - 1) :
    prodAux H (framedParamsRegPivot H r hr hL J P Q 0) k hk
      = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
          (rThresholdSplit r (H ⟨k, hk⟩) (hr ⟨k, hk⟩)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  rw [prodAux_framedParamsRegPivot_eq_threshold_prefix H r hr hL J P Q k hk hkL]
  exact prodAux_framedParamsReg_zero_aux H r hr hL P Q k hk hk1

/-- **The pivot origin product** (`Stage C` headline, the analogue of `prodAux_framedParamsReg_zero`).
At the deepest gauge slot, the pivot-aware framed product lands the threshold-ROW / `(lastLayer hL).succ`
pivot-COLUMN corner: `prod (framedParamsRegPivot 0) = reindex (rThresholdSplit r (H 0)).symm
(pivotThresholdSplit r (H last.succ) (pivotJSucc J)).symm (fromBlocks 1 0 0 0)`. The column type is
`Fin (H (lastLayer hL).succ)` here (the layer's natural `.succ` width); `deepestEPivot_base` bridges it
to `Fin (H (Fin.last L))` via the outer-reindex form `prodAux_framedParamsRegPivot_zero_outer`. Proof:
write `L = n + 1`; `prod = prodAux (n + 1)`; the last fold unfolds via `prodAux_succ_layer` (the last
layer IS the pivot corner at the origin, `framedParamsRegPivot_zero_last`), the threshold prefix
`prodAux n` is the threshold corner (`prodAux_framedParamsRegPivot_zero_prefix`), folded by
`corner_reindex_mul` (generic over the pivot right-split). -/
theorem prodAux_framedParamsRegPivot_zero {n : ℕ} (H : Fin (n + 1 + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (n + 1 + 1), r ≤ H s) (hL : 1 ≤ n + 1)
    (J : Fin r ↪ Fin (H (Fin.last (n + 1))))
    (P : (s : Fin (n + 1)) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin (n + 1)) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    prod H (framedParamsRegPivot H r hr hL J P Q 0)
      = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
          (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  -- `prod = prodAux (n+1)`; the last fold is at index `n`. (`L = n+1` is fixed in the signature, so the
  -- column type `Fin (H (lastLayer hL).succ) = Fin (H (Fin.last (n+1)))` is DEFEQ — no `subst` needed.)
  -- The two running-width identifications are `rfl` (the `prodAux_succ` `e1H/e2H` precedent).
  have e1H : H (⟨n, Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1 + 1))
      = H ((⟨n, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1)).castSucc) := rfl
  have e2H : H (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 1 + 1))
      = H ((⟨n, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1)).succ) := rfl
  -- `⟨n, _⟩ : Fin (n+1)` IS `lastLayer hL` (defeq via `lastLayer = ⟨(n+1)-1, _⟩ = ⟨n, _⟩`).
  have hlasteq : (⟨n, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1))
      = lastLayer hL := by apply Fin.ext; simp [lastLayer]
  -- `prod = prodAux (n+1)`; unfold the last fold (`prodAux_succ`, reindex-explicit form).
  show prodAux H (framedParamsRegPivot H r hr hL J P Q 0) (n + 1) (Nat.lt_succ_self (n + 1)) = _
  rw [prodAux_succ H (framedParamsRegPivot H r hr hL J P Q 0) n (Nat.lt_succ_self (n + 1)) e1H e2H]
  -- The recast last layer = `framedParamsRegPivot lastLayer` (the finCongr are identity casts;
  -- `⟨n,_⟩ = lastLayer hL` is DEFEQ at `L = n+1`, so no `rw` needed — `Matrix.ext` + `rfl`).
  have hinner : Matrix.reindex (finCongr e1H.symm) (finCongr e2H.symm)
        (framedParamsRegPivot H r hr hL J P Q 0
          (⟨n, Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1)))
      = framedParamsRegPivot H r hr hL J P Q 0 (lastLayer hL) := by
    apply Matrix.ext; intro i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply]
    rfl
  rw [hinner, framedParamsRegPivot_zero_last H r hr hL J P Q]
  -- prefix product is the threshold corner (n ≥ 1) or `1` (n = 0); fold to the pivot corner.
  -- The prefix corner's right-split index `⟨n,_⟩` is DEFEQ to `(lastLayer hL).castSucc` (L = n+1), so
  -- `corner_reindex_mul`'s interface aligns under defeq — applied in term mode (`exact`) it unifies.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- n = 0 (L = 1): `prodAux 0 = 1`; `1 * pivot-last-corner = pivot-last-corner = RHS`.
    subst hn0
    exact Matrix.one_mul _
  · -- n ≥ 1: prefix is the threshold corner at `H 0 × H ⟨n,_⟩`; fold to the pivot corner.
    rw [prodAux_framedParamsRegPivot_zero_prefix H r hr hL J P Q n
        (Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))) hnpos (by omega)]
    exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
      (rThresholdSplit r (H (⟨n, Nat.lt_of_succ_lt (Nat.lt_succ_self (n + 1))⟩ : Fin (n + 1 + 1)))
        (hr _))
      (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J))

/-- **`deepestEPivot_base`-ready form** (the Stage-C consumer): applying `deepestEPivot`'s OUTER reindex
`reindex (rThresholdSplit r (H 0)) (pivotThresholdSplit r (H (Fin.last L)) J)` to the pivot origin product
lands the corner `fromBlocks 1 0 0 0` (so the residual reads `0`). Bridges the Stage-C headline's
`(lastLayer hL).succ`-width pivot split to the `Fin (Fin.last L)`-width outer split: `pivotJSucc J = J`
(`finCongr` of the `rfl`-proof is identity) and `(lastLayer hL).succ = Fin.last L` (defeq at `L = n+1`),
so the outer reindex cancels the inner `.symm` (`Equiv.apply_symm_apply`). -/
theorem reindex_prodAux_framedParamsRegPivot_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H (framedParamsRegPivot H r hr hL J P Q 0))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  rw [prodAux_framedParamsRegPivot_zero H r hr hL J P Q]
  have hpivJ : pivotJSucc H r hL J = J := by
    apply Function.Embedding.ext; intro k
    simp only [pivotJSucc, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, finCongr_apply]
    rfl
  rw [hpivJ]
  -- `(lastLayer hL).succ = Fin.last (n+1)` (defeq); the inner pivot split IS the outer one. The two
  -- `reindex` then cancel by `apply_symm_apply` (both at the SAME `Fin.last (n+1)`-width pivot split).
  exact (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
    (pivotThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ) J)).apply_symm_apply _

end DLNFibre.DLN.RLCT
