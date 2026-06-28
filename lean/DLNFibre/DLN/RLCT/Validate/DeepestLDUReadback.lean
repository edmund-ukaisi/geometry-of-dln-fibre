import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2

/-!
# The hLDUtie readback-tie (W-a frame-conjugated dictionary)

This file isolates the ONE genuinely-delicate L=2 sub-4 residual — the matrix readback-tie that the
producer's sub-4 (`deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score`) consumes.

## The fix landed here (W-a, 2026-06-28, genm-l2conj)

The PRIOR statement (bare per-layer Schur cores, pivot `1 + readX_s`) is **numerically FALSE** — the
deepest boundary leading block is `A11 ≠ 1`, so the actual reindexed decode-layer `(1,1)`-block is
`M̄_s + readX_s` (with `M̄_s = (reindex deepestPoint_s).toBlocks₁₁`), not `1 + readX_s`. The discriminator
(r=1, H=[2,2,2], A11 = 3): bare LDU = 0.0942, Score = 0.0741.

The **W-a fix** (adjudicated, `threads/31-pin2-comparability/codex/l2-ldutie-adjudicate-*.md`; reproduced
symbolically here): the Score IS the **unframed actual-layer-pivot** core LDU. The OUTER endpoint frames
`P0/QL` cancel at the Schur level (they are the explicit triangular normalizers, `DP = DQ = 1` —
`schur_frame_transform`), so the framed Score = the UNFRAMED Schur of `reindex(prod(decode x))`, which
the two-factor LDU (`reindex_mul_schur_factor` on `layer0 · layer1 = prod(decode x)`) expands to the
unframed-layer cores `Ŝ0·(1−K̂)·Ŝ1`. This is a restatement (dictionary conjugation); the L2
kill-condition does not reopen. The exact-truth note: `Score − [unframed-actual-layer LDU] = 0`
symbolically + 3 random rational points, needing ONLY the boundary `u1 = v1 = 0` (NOT `u0·v0 = 1`).

## Route (all banked, sorry-free)

`rcore_eq_schur_of_corner_split` (hS3b: the `B`-corner removes the `+1`) → `framedSchur_eq_unframedSchur_L2`
(hPtri/hQtri/`DP = DQ = 1`: strips the OUTER frames) → `reindex_mul_schur_factor` (the two-layer LDU on
the unframed `layer0 · layer1 = prod(decode x)`) → `prod_deepestM_eq_two_of_L2` (the `L = 2` two-factor
unfold of the abstract `prod (deepestM) C`).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **W-a STEP 1-2 — the Score is the UNFRAMED Schur of `prod (decode x)`.** The Score `(1,1)`-Schur
integrand (over the framed product `endpointP0·(prod − B)·endpointQL`, pivot `(Mw₁₁+1)⁻¹`) equals the
unframed `(1,1)`-Schur complement of `reindex(prod (decode x))` over its OWN `(1,1)`-block pivot. Proven
by the banked corner-split (`hS3b` removes the `+1`) + the banked frame-strip
(`framedSchur_eq_unframedSchur_L2`, `DP = DQ = 1`). This is the W-a-true content (the bare-pivot form was
false: deepest boundary `A11 ≠ 1`); `prod_deepestM_eq_schur_ldu_readback` chains the two-layer LDU onto
this. -/
theorem score_eq_unframedSchur_prodDecode (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
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
    -- the corner: the framed `B`-product reindexes to the threshold corner (`hS3b`, supplied by the wire).
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    -- the three pivot units (derivable at the wire from the explicit normalizers / nonsingular pivots).
    (hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁)
    (hQ11inv : Invertible (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (endpointQL H hL Qf)).toBlocks₁₁)
    (hMid11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁) :
    -- The Score `(1,1)`-Schur integrand (RHS) equals the UNFRAMED Schur of `reindex(prod (decode x))`
    -- over its own `(1,1)`-block pivot (frames stripped, corner removed). This is the W-a-true target the
    -- conjugated-dictionary LHS reduces to.
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
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
                  * endpointQL H hL Qf)).toBlocks₁₂
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H ((paramsEquivFlat H).symm x))).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (prod H ((paramsEquivFlat H).symm x))).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₂ := by
  -- STEP 1: corner-split (`hS3b` removes the `+1`): the framed `(Mw₁₁+1)⁻¹` Score = Schur of the framed
  -- product `M̂ = endpointP0·prod·endpointQL` over its OWN `(1,1)` pivot.
  set eR := rThresholdSplit r (H 0) (hr 0) with heR
  set eC := pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J with heC
  set P0 := endpointP0 H hL Pf with hP0
  set QL := endpointQL H hL Qf with hQL
  set Mid := prod H ((paramsEquivFlat H).symm x) with hMid
  -- The corner split `reindex (P0·Mid·QL) = fromBlocks 1 0 0 0 + reindex (P0·(Mid−B)·QL)`.
  have hcorner : Matrix.reindex eR eC (P0 * Mid * QL)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.reindex eR eC (P0 * (Mid - B) * QL) := by
    have hsplitprod : P0 * Mid * QL = P0 * B * QL + P0 * (Mid - B) * QL := by
      rw [Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
    rw [hsplitprod]
    have hadd : Matrix.reindex eR eC (P0 * B * QL + P0 * (Mid - B) * QL)
        = Matrix.reindex eR eC (P0 * B * QL) + Matrix.reindex eR eC (P0 * (Mid - B) * QL) := by
      ext i j; simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
    rw [hadd, hS3b]
  -- `rcore_eq_schur_of_corner_split`: the producer's `(Mw₁₁+1)⁻¹` Score = Schur of `M̂` over `(M̂₁₁)⁻¹`.
  rw [rcore_eq_schur_of_corner_split (P0 * (Mid - B) * QL) (P0 * Mid * QL) eR eC hcorner]
  -- STEP 2: strip the OUTER frames (`framedSchur_eq_unframedSchur_L2`, `DP = DQ = 1`): Schur of
  -- `M̂ = P0·Mid·QL` = Schur of `Mid` (the unframed `prod (decode x)`).
  letI := hP11inv; letI := hQ11inv; letI := hMid11inv
  exact framedSchur_eq_unframedSchur_L2 H r hr hL J P0 QL Mid hPtri hQtri hP22 hQ22
    hP11inv hQ11inv hMid11inv

/-- **The unframed Schur of `prod (decode x)` IS the two-layer LDU** (`L = 2`). With `Mid = prod (decode
x) = layer0 · layer1` and the middle split `eMid = rThresholdSplit r (H 1)`, `reindex_mul_schur_factor`
expands the unframed `(1,1)`-Schur complement of `reindex(Mid)` into the LDU `Ŝ0·(1 − K̂)·Ŝ1` of the
per-layer cores read off the two reindexed decode layers (under `J = frontEmbed`, the right column split
is the threshold split, `pivotThresholdSplit_frontEmbed`). The middle pivots `Â0, Â1` and the product
pivot are invertible. -/
theorem unframedSchur_prodDecode_eq_ldu (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (A : Params (L := 2) H)
    (G0 : Matrix (Fin (H 0)) (Fin (H 1)) ℝ) (G1 : Matrix (Fin (H 1)) (Fin (H 2)) ℝ)
    (hG0 : G0 = Matrix.reindex (finCongr (rfl : H 0 = H ((0 : Fin 2)).castSucc))
        (finCongr (rfl : H 1 = H ((0 : Fin 2)).succ)) (A (0 : Fin 2)))
    (hG1 : G1 = Matrix.reindex (finCongr (rfl : H 1 = H ((1 : Fin 2)).castSucc))
        (finCongr (rfl : H 2 = H (Fin.last 2)) ) (A (1 : Fin 2)))
    [Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
        G0).toBlocks₁₁]
    [Invertible (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
        G1).toBlocks₁₁]
    [Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 2) (hr 2))
        (G0 * G1)).toBlocks₁₁] :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 2) (hr 2))
          (G0 * G1)).toBlocks₂₂
        - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 2) (hr 2))
            (G0 * G1)).toBlocks₂₁
          * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 2) (hr 2))
              (G0 * G1)).toBlocks₁₁)⁻¹
          * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 2) (hr 2))
              (G0 * G1)).toBlocks₁₂
      = ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
              G0).toBlocks₂₂
            - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                G0).toBlocks₂₁
              * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                  G0).toBlocks₁₁)⁻¹
              * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                  G0).toBlocks₁₂)
          * (1 - (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
              G1).toBlocks₂₁
              * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 2) (hr 2))
                  (G0 * G1)).toBlocks₁₁)⁻¹
              * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                  G0).toBlocks₁₂)
          * ((Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
                G1).toBlocks₂₂
            - (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
                G1).toBlocks₂₁
              * ((Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
                  G1).toBlocks₁₁)⁻¹
              * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
                  G1).toBlocks₁₂) :=
  reindex_mul_schur_factor (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
    (rThresholdSplit r (H 2) (hr 2)) G0 G1

/-- **The decode product factors as its two layers** (`L = 2`, `H : Fin 3`). The unframed middle
`Mid = prod (decode x)` equals `(layer 0) · (layer 1)` (each layer reindexed by the trivial `finCongr`
width-cast). Direct `prod_eq_prodAux_mul_last` (m = 1) with `prodAux 0 = 1`. -/
theorem prodDecode_eq_two_of_L2 (H : Fin 3 → ℕ) (A : Params (L := 2) H) :
    prod H A
      = Matrix.reindex (finCongr (rfl : H 0 = H ((0 : Fin 2)).castSucc))
            (finCongr (rfl : H 1 = H ((0 : Fin 2)).succ)) (A (0 : Fin 2))
          * Matrix.reindex (finCongr (rfl : H 1 = H ((1 : Fin 2)).castSucc))
            (finCongr (rfl : H 2 = H (Fin.last 2))) (A (1 : Fin 2)) := by
  rw [prod_eq_prodAux_mul_last (m := 1) H A rfl rfl]
  congr 1
  rw [prodAux_succ H A 0 (by omega) rfl rfl]
  exact Matrix.one_mul _

end DLNFibre.DLN.RLCT
