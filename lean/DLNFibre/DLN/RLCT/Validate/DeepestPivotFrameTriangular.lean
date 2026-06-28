import DLNFibre.DLN.RLCT.Validate.DeepestPivotFrame
import DLNFibre.DLN.RLCT.Validate.DeepestLeadingBlock
import DLNFibre.DLN.RLCT.Validate.FrontPivotProducer
import DLNFibre.Core.Matrix.RankNormalFormTriangular

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPivotFrameTriangular` — block-TRIANGULAR boundary frames

`deepestPoint_frame_pivot_exists` (`DeepestPivotFrame`) supplies the deepest-point per-layer gauge
frame family with a `B`-determined last-layer pivot, but its LAYER-0 frame is a *generic* rank-normal
left frame (`rank_normal_form_left_only`) with **no block-triangular guarantee**. The L=2 diffeo bridge
needs the endpoint frames block-triangular (`endpointP0` block-LOWER, `endpointQL` block-UPPER) — the E2
reg-preservation is FALSE at general frames (the moved core `(2,2)` block leaks into the reg reads).

This module strengthens the bundle to **block-triangular boundary frames**:
- **Layer 0** (`endpointP0`): replaced by the explicit block-LOWER normalizer
  `Core.Matrix.blockLower_left_normalizer`, whose `[Invertible A11]` precondition is the layer-0
  leading-block invertibility `deepestPoint_leadingBlock_isUnit` — **htop-conditional** (the target `B`'s
  top `r` rows full rank; supplied at the headline by the row-WLOG `rlct_infimum_rowPerm_eq`). Carries
  the same corner-normal form `hNF` (the normalizer sends `[[A11,0],[A21,0]] ↦ corM`).
- **Layer (L−1)** (`endpointQL`): the existing pivot frame is ALREADY block-UPPER — its split form is
  `fromBlocks VJ⁻¹ (−VJ⁻¹VK) 0 1` (`exists_pivotFrame_lastBlock_isUnit`), so `toBlocks₂₁ = 0` already.

So the bundle gains the two triangularity fields `hPtri`/`hQtri` the bridge consumes, under the single
extra `htop` hypothesis (the row-alignment the column-pivot WLOG's row dual provides).
-/

open Matrix
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The split-coordinate `fromBlocks 1 0 0 0` reindexed back to ambient coordinates is the block-normal
corner `corM` (the `if i = j ∧ i < r then 1 else 0` matrix). Local copy of the helper privately proven
in `DeepestGaugeConstruction`; reproven here (a self-contained `ext`) to avoid the import cycle. -/
private theorem tri_reindex_fromBlocks_one_eq_corM (r a b : ℕ) (ha : r ≤ a) (hb : r ≤ b) :
    Matrix.reindex (rThresholdSplit r a ha).symm (rThresholdSplit r b hb).symm
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
      = Matrix.of (fun (i : Fin a) (j : Fin b) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_symm]
  rcases hi : (rThresholdSplit r a ha) i with p | p <;>
    rcases hj : (rThresholdSplit r b hb) j with q | q
  · rw [Matrix.fromBlocks_apply₁₁]
    have hip : i = p.castLE ha := by
      rw [← rThresholdSplit_symm_inl r a ha p, ← hi, Equiv.symm_apply_apply]
    have hjq : j = q.castLE hb := by
      rw [← rThresholdSplit_symm_inl r b hb q, ← hj, Equiv.symm_apply_apply]
    simp only [Matrix.one_apply, Matrix.of_apply, hip, hjq, Fin.coe_castLE]
    by_cases hpq : p = q
    · subst hpq; simp [p.isLt]
    · rw [if_neg hpq, if_neg]
      rintro ⟨hval, _⟩
      exact hpq (Fin.ext hval)
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    have hjq : j = ⟨r + q, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r b hb q, ← hj, Equiv.symm_apply_apply]
    have hip : i = p.castLE ha := by
      rw [← rThresholdSplit_symm_inl r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip, hjq, Fin.coe_castLE]
    rw [if_neg]; rintro ⟨hval, hlt⟩; omega
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    have hip : i = ⟨r + p, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip]
    rw [if_neg]; rintro ⟨hval, hlt⟩; omega
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    have hip : i = ⟨r + p, by omega⟩ := by
      rw [← rThresholdSplit_symm_inr r a ha p, ← hi, Equiv.symm_apply_apply]
    simp only [Matrix.of_apply, hip]
    rw [if_neg]; rintro ⟨hval, hlt⟩; omega

/-- **The block-LOWER layer-0 frame** (the `endpointP0` triangular witness). Under `htop`, the deepest
point's layer-0 (tail columns zero, leading `r×r` block `A11` invertible) is carried to the block-normal
corner `corM` by the explicit block-LOWER unit `P := reindex⁻¹ [[⅟A11,0],[−A21⅟A11,1]]`; that `P` is a
unit, satisfies `P · layer0 = corM`, and is block-lower (`reindex P` has `toBlocks₁₂ = 0`). -/
private theorem deepest_layer0_blockLower_frame (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r) :
    ∃ P : Matrix (Fin (H (firstLayer hL).castSucc)) (Fin (H (firstLayer hL).castSucc)) ℝ,
      IsUnit P ∧
      (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
          (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _)) P).toBlocks₁₂ = 0 ∧
      P * (deepestPoint H r B hB hr hL (firstLayer hL))
        = Matrix.of (fun (i : Fin (H (firstLayer hL).castSucc)) (j : Fin (H (firstLayer hL).succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  classical
  -- Abbreviations for the layer-0 widths and matrix.
  set a := H (firstLayer hL).castSucc with ha_def
  set b := H (firstLayer hL).succ with hb_def
  have hra : r ≤ a := hr _
  have hrb : r ≤ b := hr _
  set A0 : Matrix (Fin a) (Fin b) ℝ := deepestPoint H r B hB hr hL (firstLayer hL) with hA0
  -- `firstLayer.castSucc = 0` (Fin (L+1)), so the leading-block isUnit (htop-conditional) applies.
  have hfc : (firstLayer hL).castSucc = (0 : Fin (L + 1)) := by
    apply Fin.ext; simp [firstLayer, Fin.castSucc, Fin.castAdd, Fin.castLE]
  -- The leading `r×r` block `A11` and lower-left block `A21` of `A0`.
  set A11 : Matrix (Fin r) (Fin r) ℝ :=
    A0.submatrix (Fin.castLE hra) (Fin.castLE hrb) with hA11
  set A21 : Matrix (Fin (a - r)) (Fin r) ℝ :=
    Matrix.of (fun (i : Fin (a - r)) (k : Fin r) => A0 ⟨r + i, by omega⟩ (k.castLE hrb)) with hA21
  -- `A11` is a unit (the htop-conditional leading block fact, `firstLayer.castSucc = 0`).
  have hA11unit : IsUnit A11 := by
    have h := deepestPoint_leadingBlock_isUnit H r B hB hr hL hL2 htop
    -- `deepestPoint … ⟨0,_⟩` is `A0` (since `firstLayer = ⟨0,_⟩`), and the submatrices agree.
    have hfl : (⟨0, by omega⟩ : Fin L) = firstLayer hL := by apply Fin.ext; simp [firstLayer]
    rw [hfl] at h
    -- The submatrix indices coincide (castLE on defeq widths).
    convert h using 2
  letI : Invertible A11 := hA11unit.invertible
  -- The corner-split block form: `reindex A0 = fromBlocks A11 0 A21 0` (tail columns vanish).
  have hA0blocks : Matrix.reindex (rThresholdSplit r a hra) (rThresholdSplit r b hrb) A0
      = Matrix.fromBlocks A11 (0 : Matrix (Fin r) (Fin (b - r)) ℝ) A21 0 := by
    have htail : ∀ (i : Fin a) (j : Fin b), r ≤ (j : ℕ) → A0 i j = 0 := by
      intro i j hj
      exact deepestPoint_layer0_cols_vanish H r B hB hr hL (firstLayer hL) hL2
        (by simp [firstLayer]) i j hj
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, hA11, hA21, Matrix.of_apply, Matrix.submatrix_apply, id_eq]
    · rw [rThresholdSplit_symm_inl, rThresholdSplit_symm_inl]
    · rw [rThresholdSplit_symm_inl, rThresholdSplit_symm_inr]
      exact htail _ _ (by simp only [Fin.val_mk]; omega)
    · rw [rThresholdSplit_symm_inr, rThresholdSplit_symm_inl]
    · rw [rThresholdSplit_symm_inr, rThresholdSplit_symm_inr]
      exact htail _ _ (by simp only [Fin.val_mk]; omega)
  -- The split-coordinate block-lower normalizer `P̃` and its three properties (banked).
  obtain ⟨hPtri12, hPtunit, hPtnorm⟩ := Core.Matrix.blockLower_left_normalizer (br := b - r) A11 A21
  set Pt : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (a - r)) ℝ :=
    Matrix.fromBlocks (⅟A11) 0 (-(A21 * ⅟A11)) 1 with hPt
  -- The ambient frame `P := reindex.symm P̃`.
  refine ⟨Matrix.reindex (rThresholdSplit r a hra).symm (rThresholdSplit r a hra).symm Pt, ?_, ?_, ?_⟩
  · -- `IsUnit P` from `IsUnit P̃` (reindex by an equiv preserves units).
    rw [Matrix.reindex_apply, Equiv.symm_symm]
    exact (Matrix.isUnit_submatrix_equiv _ _).mpr hPtunit
  · -- `reindex P = P̃`, so `toBlocks₁₂ = 0`.
    have hree : Matrix.reindex (rThresholdSplit r a hra) (rThresholdSplit r a hra)
        (Matrix.reindex (rThresholdSplit r a hra).symm (rThresholdSplit r a hra).symm Pt) = Pt := by
      rw [Matrix.reindex_apply, Matrix.reindex_apply, Equiv.symm_symm,
        Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rw [hree]; exact hPtri12
  · -- `P · A0 = corM`. Forward: `reindex(P·A0) = (reindex P)·(reindex A0) = P̃·(fromBlocks A11 0 A21 0)
    -- = fromBlocks 1 0 0 0` (`hPtnorm`); then apply `reindex.symm` + the corM helper.
    set P : Matrix (Fin a) (Fin a) ℝ :=
      Matrix.reindex (rThresholdSplit r a hra).symm (rThresholdSplit r a hra).symm Pt with hP_def
    -- (i) `reindex r r P = P̃`.
    have hreP : Matrix.reindex (rThresholdSplit r a hra) (rThresholdSplit r a hra) P = Pt := by
      rw [hP_def, Matrix.reindex_apply, Matrix.reindex_apply, Equiv.symm_symm,
        Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    -- (ii) the product reindexes: `reindex r r' (P·A0) = (reindex r r P)·(reindex r r' A0)`.
    have hmul : Matrix.reindex (rThresholdSplit r a hra) (rThresholdSplit r b hrb) (P * A0)
        = (Matrix.reindex (rThresholdSplit r a hra) (rThresholdSplit r a hra) P)
          * (Matrix.reindex (rThresholdSplit r a hra) (rThresholdSplit r b hrb) A0) := by
      simp only [Matrix.reindex_apply]
      exact (Matrix.submatrix_mul_equiv P A0 (rThresholdSplit r a hra).symm
        (rThresholdSplit r a hra).symm (rThresholdSplit r b hrb).symm).symm
    -- (iii) combine: `reindex (P·A0) = fromBlocks 1 0 0 0`.
    have hprod : Matrix.reindex (rThresholdSplit r a hra) (rThresholdSplit r b hrb) (P * A0)
        = Matrix.fromBlocks 1 0 0 0 := by
      rw [hmul, hreP, hA0blocks, hPtnorm]
    -- (iv) un-reindex via the reindex EQUIV's `symm_apply_apply` round-trip, then the corM helper.
    have hround := (Matrix.reindex (rThresholdSplit r a hra)
      (rThresholdSplit r b hrb)).symm_apply_apply (P * A0)
    rw [hprod] at hround
    rw [← hround, Matrix.reindex_symm, tri_reindex_fromBlocks_one_eq_corM r a b hra hrb]

/-- **The block-triangular deepest-point boundary-frame bundle** (L=2 bridge precondition). Under the
row-alignment `htop` (target `B`'s top `r` rows full rank), the deepest-point per-layer gauge frame
family can be taken with **block-LOWER layer-0** (`endpointP0`) and **block-UPPER layer-(L−1)**
(`endpointQL`) endpoint frames, retaining all of `deepestPoint_frame_pivot_exists`'s conclusions
(boundary triviality, corner-normal form, the pivot-corner unit `B22`, the last-layer corner) and adding
the two triangularity facts `hPtri`/`hQtri`. -/
theorem deepestPoint_frame_pivot_triangular_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    -- Front-pivot hypothesis about the producer bundle's `.choose` pivot, threaded so the output `J`
    -- (which IS that pivot) carries the front-embed identity the consumer needs.
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr) :
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
      -- **hPtri**: layer-0 endpoint frame `P (firstLayer)` is block-LOWER under the threshold split.
      (Matrix.reindex (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
          (rThresholdSplit r (H (firstLayer hL).castSucc) (hr _))
          (P (firstLayer hL))).toBlocks₁₂ = 0 ∧
      -- **hQtri**: layer-(L−1) endpoint frame `Q (lastLayer)` is block-UPPER under the pivot split.
      (Matrix.reindex (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) J)
          (Q (lastLayer hL))).toBlocks₂₁ = 0 := by
  classical
  -- The (now block-upper-aware) producer bundle — use `.choose`/`.choose_spec` so the output `J` IS
  -- the producer's `.choose` pivot, and the threaded `hJfront` (about `.choose`) is its front-identity.
  set J := (deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose with hJ_def
  obtain ⟨P0, Q0, hPunit0, hQunit0, hQf0, hPfL, hNF0, hQf22, hcorner, hQUpper⟩ :=
    (deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose_spec
  -- The block-LOWER layer-0 frame (htop-conditional).
  obtain ⟨P0new, hP0new_unit, hP0new_tri, hP0new_nf⟩ :=
    deepest_layer0_blockLower_frame H r B hB hr hL hL2 htop
  -- `firstLayer ≠ lastLayer` (`2 ≤ L`).
  have hfne : firstLayer hL ≠ lastLayer hL := by
    intro h; have := congrArg Fin.val h; simp only [firstLayer, lastLayer] at this; omega
  -- The new frame family: `P0` with layer-0 overridden by the block-lower frame.
  refine ⟨J, Function.update P0 (firstLayer hL) P0new, Q0, hJfront, ?_, hQunit0, hQf0, ?_, ?_, hQf22,
    hcorner, ?_, hQUpper⟩
  · -- `IsUnit (P s)`: `P0new` at firstLayer, `P0` elsewhere.
    intro s
    by_cases hs : s = firstLayer hL
    · subst hs; rw [Function.update_self]; exact hP0new_unit
    · rw [Function.update_of_ne hs]; exact hPunit0 s
  · -- `P (lastLayer) = 1`: `lastLayer ≠ firstLayer`, so `P lastLayer = P0 lastLayer = 1`.
    rw [Function.update_of_ne (Ne.symm hfne)]; exact hPfL
  · -- `hNF`: `P s · deepest s · Q s = corM` for `(s:ℕ)+1 ≠ L`. At firstLayer use the new frame's NF
    -- (`Q firstLayer = 1`); elsewhere the producer's `hNF0`.
    intro s hs
    by_cases hsf : s = firstLayer hL
    · subst hsf
      rw [Function.update_self, hQf0, Matrix.mul_one]
      exact hP0new_nf
    · rw [Function.update_of_ne hsf]; exact hNF0 s hs
  · -- `hPtri`: `P firstLayer = P0new` is block-lower.
    rw [Function.update_self]; exact hP0new_tri

end DLNFibre.DLN.RLCT
