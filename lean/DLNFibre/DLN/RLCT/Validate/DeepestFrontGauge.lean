import DLNFibre.DLN.RLCT.Validate.DeepestLastBlock
import DLNFibre.DLN.RLCT.Validate.DeepestPivotFrameTriangular

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge` — the FRONT-pivot triangular bundle (genm-44l2, phase C)

The front-pivot parallel of the deepest-point triangular frame bundle. It replaces the unprovable
`hJfront` (the arbitrary `deepestPoint_frame_pivot_exists.choose = frontEmbed`) with the PROVABLE
precursor `hcolfront` (`B`'s front `r` columns full rank — the column-WLOG `headline_frontRowColPivot_exists`
supplies it at the headline ⨅, the dual of `htop`).

The last-layer pivot is built by the FRONT frame builder `exists_frontPivotFrame_lastBlock_isUnit`
(`J = frontEmbed`, DETERMINISTIC), whose `hfront` precursor is the column-dual
`deepestPoint_lastBlock_front_rank` (`DeepestLastBlock`). The layer-0 (htop) arm reuses the banked
`deepest_layer0_blockLower_frame` (`DeepestPivotFrameTriangular`, now public) VERBATIM. So the front
triangular bundle has the SAME conclusion shape as `deepestPoint_frame_pivot_triangular_exists`, with
`J.trans finCongr = frontEmbed` HOLDING BY CONSTRUCTION (not threaded).
-/

open Matrix
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The deepest-point last-layer FRONT pivot frame** (the front analog of
`exists_deepest_lastLayer_pivotFrame`, genm-44l2). Built from `exists_frontPivotFrame_lastBlock_isUnit`
with the `hfront` precursor = the column-dual `deepestPoint_lastBlock_front_rank` (`hcolfront`). The
pivot `J` IS the front embedding `⟨Fin.castLE _, _⟩` — DETERMINISTIC, not an arbitrary choose. -/
theorem exists_deepest_lastLayer_frontPivotFrame (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r) :
    ∃ Q : Matrix (Fin (H ((lastLayer hL).succ))) (Fin (H ((lastLayer hL).succ))) ℝ,
      IsUnit Q ∧
      IsUnit ((Matrix.reindex
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
            ⟨Fin.castLE (hr ((lastLayer hL).succ)), Fin.castLE_injective (hr ((lastLayer hL).succ))⟩)
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
            ⟨Fin.castLE (hr ((lastLayer hL).succ)), Fin.castLE_injective (hr ((lastLayer hL).succ))⟩)
          Q).toBlocks₂₂) ∧
      Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).castSucc)) (hr _))
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
            ⟨Fin.castLE (hr ((lastLayer hL).succ)), Fin.castLE_injective (hr ((lastLayer hL).succ))⟩)
          (deepestPoint H r B hB hr hL (lastLayer hL) * Q)
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 ∧
      (Matrix.reindex
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
            ⟨Fin.castLE (hr ((lastLayer hL).succ)), Fin.castLE_injective (hr ((lastLayer hL).succ))⟩)
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
            ⟨Fin.castLE (hr ((lastLayer hL).succ)), Fin.castLE_injective (hr ((lastLayer hL).succ))⟩)
          Q).toBlocks₂₁ = 0 ∧
      (Matrix.reindex
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
            ⟨Fin.castLE (hr ((lastLayer hL).succ)), Fin.castLE_injective (hr ((lastLayer hL).succ))⟩)
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
            ⟨Fin.castLE (hr ((lastLayer hL).succ)), Fin.castLE_injective (hr ((lastLayer hL).succ))⟩)
          Q).toBlocks₂₂
        = (1 : Matrix (Fin (H ((lastLayer hL).succ) - r)) (Fin (H ((lastLayer hL).succ) - r)) ℝ) := by
  -- `A := deepestPoint (lastLayer)`; tail ROWS vanish (`2 ≤ L`).
  have hsL : ((lastLayer hL : Fin L) : ℕ) + 1 = L := by simp only [lastLayer]; omega
  have htail : ∀ (i : Fin (H ((lastLayer hL).castSucc))) (j : Fin (H ((lastLayer hL).succ))),
      r ≤ (i : ℕ) → deepestPoint H r B hB hr hL (lastLayer hL) i j = 0 :=
    fun i j hi => (deepestPoint_isDeep H r B hB hr hL).2.2.2.2 (lastLayer hL) hL2 hsL i j hi
  -- The `hfront` precursor: the top-left `r×r` block of the last layer is full rank (column-dual).
  -- `((A.submatrix castLE id).submatrix id castLE) = A.submatrix castLE castLE` (submatrix_submatrix).
  have hfront : (((deepestPoint H r B hB hr hL (lastLayer hL)).submatrix
        (Fin.castLE (hr (lastLayer hL).castSucc) : Fin r → Fin (H (lastLayer hL).castSucc))
        (id : Fin (H ((lastLayer hL).succ)) → Fin (H ((lastLayer hL).succ)))).submatrix
        (id : Fin r → Fin r)
        (Fin.castLE (hr ((lastLayer hL).succ)) : Fin r → Fin (H ((lastLayer hL).succ)))).rank = r := by
    rw [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
    exact deepestPoint_lastBlock_front_rank H r B hB hr hL hL2 hcolfront
  exact exists_frontPivotFrame_lastBlock_isUnit (hr _) (hr _)
    (deepestPoint H r B hB hr hL (lastLayer hL)) htail hfront

/-- The front last-layer pivot embedding `⟨Fin.castLE _, _⟩ : Fin r ↪ Fin (H ((lastLayer hL).succ))`. -/
private noncomputable def frontJsucc (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : Fin r ↪ Fin (H ((lastLayer hL).succ)) :=
  ⟨Fin.castLE (hr ((lastLayer hL).succ)), Fin.castLE_injective (hr ((lastLayer hL).succ))⟩

/-- **`frontJsucc` transports to `frontEmbed`** under the `H_lastLayer_succ` cast: `(frontJsucc).trans
(finCongr (H_lastLayer_succ)).toEmbedding = frontEmbed`. Both are `k ↦ k` (value-preserving). -/
private theorem frontJsucc_trans_eq_frontEmbed (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (frontJsucc H r hr hL).trans (finCongr (H_lastLayer_succ H hL)).toEmbedding
      = frontEmbed H r hr := by
  apply Function.Embedding.ext
  intro k
  simp only [frontJsucc, frontEmbed, Function.Embedding.trans_apply, finCongr_apply,
    Equiv.coe_toEmbedding, Function.Embedding.coeFn_mk]
  apply Fin.ext
  simp [Fin.castLE]

/-- **The deepest-point FRONT pivot frame family** (the front analog of `deepestPoint_frame_pivot_exists`).
Same per-layer family — `deepestPoint_frame` off the last layer, the FRONT pivot frame on it — but the
last-layer pivot `J = frontJsucc` is the front embedding (DETERMINISTIC, from
`exists_deepest_lastLayer_frontPivotFrame` + `hcolfront`), NOT the arbitrary `.choose`. The extra first
conjunct `J = frontJsucc` pins it. -/
theorem deepestPoint_frame_pivot_front_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r) :
    ∃ (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
      (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ),
      (∀ s : Fin L, IsUnit (P s)) ∧ (∀ s : Fin L, IsUnit (Q s)) ∧
      Q (firstLayer hL)
          = (1 : Matrix (Fin (H (firstLayer hL).succ)) (Fin (H (firstLayer hL).succ)) ℝ) ∧
      P (lastLayer hL)
          = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ) ∧
      (∀ s : Fin L, (s : ℕ) + 1 ≠ L →
        P s * (deepestPoint H r B hB hr hL s) * Q s
          = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
              if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) ∧
      IsUnit ((Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _)
          (frontJsucc H r hr hL))
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (frontJsucc H r hr hL))
          (Q (lastLayer hL))).toBlocks₂₂) ∧
      Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).castSucc)) (hr _))
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (frontJsucc H r hr hL))
          ((deepestPoint H r B hB hr hL (lastLayer hL)) * Q (lastLayer hL))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 ∧
      (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (frontJsucc H r hr hL))
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (frontJsucc H r hr hL))
          (Q (lastLayer hL))).toBlocks₂₁ = 0 ∧
      (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (frontJsucc H r hr hL))
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (frontJsucc H r hr hL))
          (Q (lastLayer hL))).toBlocks₂₂
        = (1 : Matrix (Fin (H ((lastLayer hL).succ) - r)) (Fin (H ((lastLayer hL).succ) - r)) ℝ) := by
  classical
  obtain ⟨QL, hQLunit, hB22, hcorner, hQUpper, hB22one⟩ :=
    exists_deepest_lastLayer_frontPivotFrame H r B hB hr hL hL2 hcolfront
  -- The frame family: `deepestPoint_frame` off the last layer; the FRONT pivot `QL` on it.
  set Qpiv : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ :=
    fun s => if h : s = lastLayer hL then h ▸ QL else (deepestPoint_frame H r B hB hr hL s).2
    with hQpiv
  have hQlast : Qpiv (lastLayer hL) = QL := by simp only [hQpiv, dif_pos rfl]
  refine ⟨fun s => (deepestPoint_frame H r B hB hr hL s).1, Qpiv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; exact (deepestPoint_frame_invertible H r B hB hr hL s).1
  · intro s
    by_cases hs : s = lastLayer hL
    · subst hs; rw [hQlast]; exact hQLunit
    · simp only [hQpiv, dif_neg hs]; exact (deepestPoint_frame_invertible H r B hB hr hL s).2
  · have hfirst : firstLayer hL ≠ lastLayer hL := by
      intro h; have := congrArg (Fin.val) h; simp only [firstLayer, lastLayer] at this; omega
    simp only [hQpiv, dif_neg hfirst]
    exact deepestPoint_frame_Qf_eq_one H r B hB hr hL (firstLayer hL) hL2 (by simp [firstLayer])
  · exact deepestPoint_frame_Pf_eq_one H r B hB hr hL (lastLayer hL) hL2
      (by simp only [lastLayer]; omega)
  · intro s hs
    have hsl : s ≠ lastLayer hL := by
      intro h; subst h; simp only [lastLayer] at hs; omega
    simp only [hQpiv, dif_neg hsl]
    exact deepestPoint_frame_normal H r B hB hr hL s
  · rw [hQlast]; exact hB22
  · rw [hQlast]; exact hcorner
  · rw [hQlast]; exact hQUpper
  · rw [hQlast]; exact hB22one

/-- **The deepest-point FRONT block-triangular boundary-frame bundle** (genm-44l2, the `hJfront`-free
analog of `deepestPoint_frame_pivot_triangular_exists`). Same OUTPUT signature as the arbitrary
triangular bundle, but built from `deepestPoint_frame_pivot_front_exists` (last-layer pivot
`J = frontJsucc`, DETERMINISTIC, from `hcolfront`) + the banked `deepest_layer0_blockLower_frame`
(layer-0, from `htop`, reused verbatim). The front-embed identity `J.trans finCongr = frontEmbed` holds
BY CONSTRUCTION (`frontJsucc_trans_eq_frontEmbed`) — NOT threaded. So a consumer gets the SAME bundle
the gauge construction needs, with `hJfront` replaced by the provable `hcolfront`. -/
theorem deepestPoint_frame_pivot_triangular_front_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r) :
    ∃ (J : Fin r ↪ Fin (H ((lastLayer hL).succ)))
      (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
      (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ),
      J.trans (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr ∧
      (∀ s : Fin L, IsUnit (P s)) ∧ (∀ s : Fin L, IsUnit (Q s)) ∧
      Q (firstLayer hL)
          = (1 : Matrix (Fin (H (firstLayer hL).succ)) (Fin (H (firstLayer hL).succ)) ℝ) ∧
      P (lastLayer hL)
          = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ) ∧
      (∀ s : Fin L, (s : ℕ) + 1 ≠ L →
        P s * (deepestPoint H r B hB hr hL s) * Q s
          = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
              if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) ∧
      IsUnit ((Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (Q (lastLayer hL))).toBlocks₂₂) ∧
      Matrix.reindex (rThresholdSplit r (H ((lastLayer hL).castSucc)) (hr _))
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          ((deepestPoint H r B hB hr hL (lastLayer hL)) * Q (lastLayer hL))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 ∧
      (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
          (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
          (P (firstLayer hL))).toBlocks₁₂ = 0 ∧
      (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (Q (lastLayer hL))).toBlocks₂₁ = 0 ∧
      (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
          (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
          (P (firstLayer hL))).toBlocks₂₂
        = (1 : Matrix (Fin (H (firstLayer hL).castSucc - r)) (Fin (H (firstLayer hL).castSucc - r)) ℝ) ∧
      (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (Q (lastLayer hL))).toBlocks₂₂
        = (1 : Matrix (Fin (H ((lastLayer hL).succ) - r)) (Fin (H ((lastLayer hL).succ) - r)) ℝ) := by
  classical
  -- The FRONT pivot frame family (last-layer `J = frontJsucc`, from `hcolfront`).
  obtain ⟨P0, Q0, hPunit0, hQunit0, hQf0, hPfL, hNF0, hQf22, hcorner, hQUpper, hQf22one⟩ :=
    deepestPoint_frame_pivot_front_exists H r B hB hr hL hL2 hcolfront
  -- The block-LOWER layer-0 frame (htop-conditional, banked, reused verbatim).
  obtain ⟨P0new, hP0new_unit, hP0new_tri, hP0new_nf, hP0new_22one⟩ :=
    deepest_layer0_blockLower_frame H r B hB hr hL hL2 htop
  have hfne : firstLayer hL ≠ lastLayer hL := by
    intro h; have := congrArg Fin.val h; simp only [firstLayer, lastLayer] at this; omega
  refine ⟨frontJsucc H r hr hL, Function.update P0 (firstLayer hL) P0new, Q0,
    frontJsucc_trans_eq_frontEmbed H r hr hL, ?_, hQunit0, hQf0, ?_, ?_, hQf22,
    hcorner, ?_, hQUpper, ?_, hQf22one⟩
  · intro s
    by_cases hs : s = firstLayer hL
    · subst hs; rw [Function.update_self]; exact hP0new_unit
    · rw [Function.update_of_ne hs]; exact hPunit0 s
  · rw [Function.update_of_ne (Ne.symm hfne)]; exact hPfL
  · intro s hs
    by_cases hsf : s = firstLayer hL
    · subst hsf
      rw [Function.update_self, hQf0, Matrix.mul_one]
      exact hP0new_nf
    · rw [Function.update_of_ne hsf]; exact hNF0 s hs
  · rw [Function.update_self]; exact hP0new_tri
  · rw [Function.update_self]; exact hP0new_22one

end DLNFibre.DLN.RLCT
