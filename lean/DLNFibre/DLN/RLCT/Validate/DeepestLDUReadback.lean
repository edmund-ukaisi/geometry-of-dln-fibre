import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2

/-!
# The hLDUtie readback-tie (W-a frame-conjugated dictionary)

This file isolates the ONE genuinely-delicate L=2 sub-4 residual — the matrix readback-tie that the
producer's sub-4 (`deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score`) consumes.

## The fix landed here (W-a, 2026-06-28, genm-l2conj)

The PRIOR statement (bare per-layer Schur cores, pivot `1 + gaugeReadX_s`) is **numerically FALSE** — the
deepest boundary leading block is `A11 ≠ 1`, so the actual reindexed decode-layer `(1,1)`-block is
`M̄_s + gaugeReadX_s` (with `M̄_s = (reindex deepestPoint_s).toBlocks₁₁`), not `1 + gaugeReadX_s`. The discriminator
(r=1, H=[2,2,2], A11 = 3): bare LDU = 0.0942, Score = 0.0741.

The **W-a fix** (adjudicated, `threads/31-pin2-comparability/codex/l2-ldutie-adjudicate-*.md`; reproduced
symbolically here): the Score IS the **unframed actual-layer-pivot** core LDU. The OUTER endpoint frames
`P0/QL` cancel at the Schur level (they are the explicit triangular normalizers, `DP = DQ = 1` —
`schur_frame_transform`), so the framed Score = the UNFRAMED Schur of `reindex(prod(decode x))`, which
the two-factor LDU (`reindex_mul_schur_factor` on `layer0 · layer1 = prod(decode x)`) expands to the
unframed-layer cores `S0c·(1−Kc)·S1c`. This is a restatement (dictionary conjugation); the L2
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
expands the unframed `(1,1)`-Schur complement of `reindex(Mid)` into the LDU `S0c·(1 − Kc)·S1c` of the
per-layer cores read off the two reindexed decode layers (under `J = frontEmbed`, the right column split
is the threshold split, `pivotThresholdSplit_frontEmbed`). The middle pivots `Â0, Â1` and the product
pivot are invertible. -/
theorem unframedSchur_prodDecode_eq_ldu (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s)
    (G0 : Matrix (Fin (H 0)) (Fin (H 1)) ℝ) (G1 : Matrix (Fin (H 1)) (Fin (H 2)) ℝ)
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

/-- **The hLDUtie readback-tie, W-a CONJUGATED dictionary** (standalone, sub-4's matrix-equality
residual). The reduced two-layer core product `prod (deepestM) C` over the **conjugated**
(actual-layer-pivot) core tuple `C` — whose two layers read back as the unframed Schur cores
`C 0 = S0c`, `C 1 = (1 − Kc)·S1c` of the reindexed decode layers (`hC0`/`hC1`, supplied by the producer's
conjugated reads at the wire) — equals the Score `(1,1)`-Schur integrand over the framed reindexed
product. TRUE (the bare-pivot form was false: deepest boundary `A11 ≠ 1`).

Proof: `prod_deepestM_eq_two_of_L2` (the abstract two-factor unfold) + `hC0`/`hC1` reduce the LHS to the
LDU `S0c·(1 − Kc)·S1c`; `prodDecode_eq_two_of_L2` + `unframedSchur_prodDecode_eq_ldu` identify that LDU
with the unframed Schur of `prod (decode x)`; `score_eq_unframedSchur_prodDecode` identifies that with the
Score. -/
theorem prod_deepestM_eq_schur_ldu_readback (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
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
    (x : Fin (flatDim H) → ℝ)
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁)
    (hQ11inv : Invertible (Matrix.reindex (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (endpointQL H hL Qf)).toBlocks₁₁)
    (hMid11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
        (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁)
    -- the layer-pivot invertibilities (decode layers have nonzero leading block near the deepest point).
    (hA0inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
        (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁)
    (hA1inv : Invertible (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
        (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₁₁)
    -- the conjugated tuple `C`, with the two readback conditions (supplied by the conjugated producer).
    (C : Params (L := 2) (deepestM H r))
    (hC0 : Matrix.reindex (finCongr (rfl : deepestM H r 0 = deepestM H r ((0 : Fin 2)).castSucc))
        (finCongr (rfl : deepestM H r 1 = deepestM H r ((0 : Fin 2)).succ)) (C (0 : Fin 2))
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
            (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
              (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
                (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂)
    (hC1 : Matrix.reindex (finCongr (rfl : deepestM H r 1 = deepestM H r ((1 : Fin 2)).castSucc))
        (finCongr (rfl : deepestM H r (Fin.last 2) = deepestM H r ((1 : Fin 2)).succ)) (C (1 : Fin 2))
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
                  (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₁₂)) :
    prod (deepestM H r) C
      = Matrix.of (fun i j => ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
              * endpointQL H hL Qf)).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                * endpointQL H hL Qf)).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₂) i j) := by
  -- `eC = rThresholdSplit r (H 2)` under `J = frontEmbed` (`pivotThresholdSplit_frontEmbed`).
  have heC : pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J
      = rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) := by
    rw [hJfront]; exact pivotThresholdSplit_frontEmbed H r hr
  -- The two decode layers as bare matrices (their `Fin`-index types are defeq to `H 0/1/2`).
  set L0 : Matrix (Fin (H 0)) (Fin (H 1)) ℝ := ((paramsEquivFlat H).symm x) (0 : Fin 2) with hL0
  set L1 : Matrix (Fin (H 1)) (Fin (H 2)) ℝ := ((paramsEquivFlat H).symm x) (1 : Fin 2) with hL1
  -- `Mid = prod (decode x) = L0 · L1` (the trivial `finCongr` reindexes collapse).
  have hMidfac : prod H ((paramsEquivFlat H).symm x) = L0 * L1 := by
    rw [prodDecode_eq_two_of_L2 H ((paramsEquivFlat H).symm x)]
    simp only [finCongr_refl, Matrix.reindex_refl_refl, hL0, hL1]
  -- The product-pivot invertibility on `L0 · L1` (= `hMid11inv` after `heC` + `hMidfac`).
  letI := hA0inv; letI := hA1inv
  letI hMidLDU : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
      (rThresholdSplit r (H 2) (hr 2)) (L0 * L1)).toBlocks₁₁ := by
    rw [heC] at hMid11inv; rw [hMidfac] at hMid11inv; exact hMid11inv
  -- The LDU of the unframed Schur of `L0 · L1`.
  have hldu := unframedSchur_prodDecode_eq_ldu H r hr L0 L1
  -- The Score (RHS) = unframed Schur of `Mid` (= `L0·L1`).
  have hscore := score_eq_unframedSchur_prodDecode H r B hB hr hL (rfl) J hJfront Pf Qf
    hPtri hQtri hP22 hQ22 x hS3b hP11inv hQ11inv hMid11inv
  -- Normalize to a common middle `unframed Schur [rThr, prod(decode x)]`: `heC` collapses hscore's
  -- `pivotThr ↦ rThr` (BOTH its Score-leak LHS and unframed-Schur RHS); `← hMidfac` folds hldu's product
  -- pivot `L0·L1 ↦ prod` (the separate `L0`/`L1` core reads untouched).
  rw [heC] at hscore
  rw [← hMidfac] at hldu
  -- LHS `prod(deepestM) C` unfolds (via `hC0`/`hC1`) to `S0c·((1−Kc)·S1c)` (right-assoc); hldu's RHS is
  -- the LEFT-assoc `S0c·(1−Kc)·S1c`. Bridge by `Matrix.mul_assoc` (the THREE explicit top-level factors
  -- the LDU reads off `L0`/`L1`), so the LDU entry from hldu matches the unfolded LHS.
  rw [prod_deepestM_eq_two_of_L2 H r C, hC0, hC1]
  rw [Matrix.mul_assoc
    ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) L0).toBlocks₂₂
      - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) L0).toBlocks₂₁
        * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) L0).toBlocks₁₁)⁻¹
        * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) L0).toBlocks₁₂)] at hldu
  -- Now hldu : `unframed Schur [rThr, prod] = S0c · ((1−Kc) · S1c)` — entrywise it ties the goal RHS
  -- (`ScoreLeak`, via hscore) to the unfolded LHS. The split widths `H (Fin.last 2)`/`H 2` are defeq.
  ext i j
  rw [Matrix.of_apply, heC]
  have hsc := congrFun (congrFun hscore i) j
  have hld := congrFun (congrFun hldu i) j
  rw [hsc]
  exact hld.symm

/-! ## The dict-match keystone (the conjugated producer discharges the readback hyps)

The W-a-true readback `prod_deepestM_eq_schur_ldu_readback` consumes `C` via `hC0`/`hC1` that read the
conjugated cores off the reindexed decode layers. This keystone shows the B-threaded conjugated producer
(`schurCorrectionConj`) supplies exactly that: at the deepest-split point, the reindexed decode layer's
blocks split additively as `deepBlk_s + read_s` (`reindex_fromBlocks_reads_eq_deviation` +
`reindex(decode w) = reindex(deepest) + reindex(deviation)`), so the absorbed core
`decode(q).core_s + schurCorrectionConj_s` equals that layer's `(1,1)`-Schur core. -/

/-- **Per-layer additive block-split.** At the deepest-split point `q = deepestSplit w0 w` (`w0 = the
deepest-point flat image`), the reindexed decode layer `reindex(decode w)_s` has blocks `deepBlk·_s +
read·_s`: the deepest layer block plus the gauge/core deviation read. (`reindex` is additive;
`reindex(deviation) = fromBlocks(reads)` is `reindex_fromBlocks_reads_eq_deviation`.) -/
theorem reindex_decode_blocks_split (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (w : Fin (flatDim H) → ℝ) (s : Fin L) :
    Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (((paramsEquivFlat H).symm w) s)
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
          (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)
        + Matrix.fromBlocks
            (gaugeReadX H r hr hL ((deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).1,
              (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).2.2) s)
            (gaugeReadY H r hr hL ((deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).1,
              (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).2.2) s)
            (gaugeReadZ H r hr hL ((deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).1,
              (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).2.2) s)
            ((paramsEquivFlat (deepestM H r)).symm
              (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).2.1 s) := by
  set w0 := (paramsEquivFlat H) (deepestPoint H r B hB hr hL) with hw0
  -- `decode w = deepest + decode (w − w0)` (paramsEquivFlat.symm is additive; `decode w0 = deepest`).
  have hdecode : ((paramsEquivFlat H).symm w) s
      = (deepestPoint H r B hB hr hL) s + ((paramsEquivFlat H).symm (w - w0)) s := by
    have hlin : ∀ y, (paramsEquivFlat H).symm y = (paramsEquivFlatLinear H).symm y := fun y => by
      apply (paramsEquivFlatLinear H).injective
      rw [(paramsEquivFlatLinear H).apply_symm_apply,
        show (paramsEquivFlatLinear H) ((paramsEquivFlat H).symm y)
          = (paramsEquivFlat H) ((paramsEquivFlat H).symm y) from
          congrFun (paramsEquivFlatLinear_coe H) _, (paramsEquivFlat H).apply_symm_apply]
    have hw0d : (paramsEquivFlat H).symm w0 = deepestPoint H r B hB hr hL := by
      rw [hw0, (paramsEquivFlat H).symm_apply_apply]
    have hsum : (paramsEquivFlat H).symm w
        = (paramsEquivFlat H).symm w0 + (paramsEquivFlat H).symm (w - w0) := by
      rw [hlin w, hlin w0, hlin (w - w0), ← map_add]
      congr 1; abel
    rw [hsum, hw0d]
    show (deepestPoint H r B hB hr hL + (paramsEquivFlat H).symm (w - w0)) s
        = deepestPoint H r B hB hr hL s + (paramsEquivFlat H).symm (w - w0) s
    rfl
  -- `reindex (deepest + dev) = reindex deepest + reindex dev` (`submatrix` is additive).
  rw [hdecode]
  rw [show Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        ((deepestPoint H r B hB hr hL) s + ((paramsEquivFlat H).symm (w - w0)) s)
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
          (rThresholdSplit r (H s.succ) (hr s.succ)) ((deepestPoint H r B hB hr hL) s)
        + Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
          (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm (w - w0)) s) from by
    simp only [Matrix.reindex_apply]; rfl]
  congr 1
  rw [← reindex_fromBlocks_reads_eq_deviation H r hr hL w0 w s]
  rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]

/-- **The dict-match keystone** (the conjugated producer = the reindexed-decode-layer Schur core). For a
BOUNDARY layer `s` (deepest `(2,2)`-block `deepBlkT_s = 0`, i.e. `hT`), the absorbed core
`decode(q).core_s + schurCorrectionConj_s` (at the deepest-split point `q = deepestSplit w0 w`) equals the
`(1,1)`-Schur core of the reindexed decode layer `reindex(decode w)_s` — exactly the `conjCore` the
standalone's `hC0`/`hC1` read. So the B-threaded conjugated producer discharges those readback
hypotheses. (`deepBlkT_s = 0` holds at both `L = 2` layers — layer-0 cols ≥ r vanish, layer-(L−1) rows ≥
r vanish.) -/
theorem absorbedCoreConj_eq_schurCore (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (w : Fin (flatDim H) → ℝ) (s : Fin L)
    (hT : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0) :
    (paramsEquivFlat (deepestM H r)).symm
        (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).2.1 s
      + schurCorrectionConj H r B hB hr hL
          ((deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).1,
            (deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w).2.2) s
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
            (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
              (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
                (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₁₁)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
                (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₁₂ := by
  set q := deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w with hq
  set MD := Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
      (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s) with hMD
  set FB := Matrix.fromBlocks (gaugeReadX H r hr hL (q.1, q.2.2) s) (gaugeReadY H r hr hL (q.1, q.2.2) s)
      (gaugeReadZ H r hr hL (q.1, q.2.2) s) ((paramsEquivFlat (deepestM H r)).symm q.2.1 s) with hFB
  -- The reindexed decode layer's blocks split as `MD + FB` (`reindex_decode_blocks_split`).
  have hsplit := reindex_decode_blocks_split H r B hB hr hL w s
  rw [← hMD, ← hFB] at hsplit
  rw [hsplit]
  -- The four block reads of `MD + FB` (`MD = reindex deepest` whose `(2,2)` vanishes by `hT`; `FB`'s
  -- blocks ARE the reads). `toBlocks` is additive entrywise; `FB.toBlocks·· = the read`.
  have h22 : (MD + FB).toBlocks₂₂ = (paramsEquivFlat (deepestM H r)).symm q.2.1 s := by
    funext i j
    have hMD22 : MD.toBlocks₂₂ i j = 0 := by rw [hMD] at hT ⊢; rw [hT]; rfl
    show MD (Sum.inr i) (Sum.inr j) + FB (Sum.inr i) (Sum.inr j) = _
    have : MD (Sum.inr i) (Sum.inr j) = 0 := hMD22
    rw [this, zero_add, hFB, Matrix.fromBlocks_apply₂₂]
  have h21 : (MD + FB).toBlocks₂₁ = deepBlkZ H r B hB hr hL s + gaugeReadZ H r hr hL (q.1, q.2.2) s := by
    funext i j
    show MD (Sum.inr i) (Sum.inl j) + FB (Sum.inr i) (Sum.inl j) = _
    rw [hFB, Matrix.fromBlocks_apply₂₁]; rfl
  have h11 : (MD + FB).toBlocks₁₁ = deepBlkA H r B hB hr hL s + gaugeReadX H r hr hL (q.1, q.2.2) s := by
    funext i j
    show MD (Sum.inl i) (Sum.inl j) + FB (Sum.inl i) (Sum.inl j) = _
    rw [hFB, Matrix.fromBlocks_apply₁₁]; rfl
  have h12 : (MD + FB).toBlocks₁₂ = deepBlkY H r B hB hr hL s + gaugeReadY H r hr hL (q.1, q.2.2) s := by
    funext i j
    show MD (Sum.inl i) (Sum.inr j) + FB (Sum.inl i) (Sum.inr j) = _
    rw [hFB, Matrix.fromBlocks_apply₁₂]; rfl
  rw [h22, h21, h11, h12, schurCorrectionConj]
  -- `decode core + (−Z·A⁻¹·Y) = decode core − Z·A⁻¹·Y` (`neg_mul` twice + `sub_eq_add_neg`).
  rw [show -(deepBlkZ H r B hB hr hL s + gaugeReadZ H r hr hL (q.1, q.2.2) s)
        * (deepBlkA H r B hB hr hL s + gaugeReadX H r hr hL (q.1, q.2.2) s)⁻¹
        * (deepBlkY H r B hB hr hL s + gaugeReadY H r hr hL (q.1, q.2.2) s)
      = -((deepBlkZ H r B hB hr hL s + gaugeReadZ H r hr hL (q.1, q.2.2) s)
        * (deepBlkA H r B hB hr hL s + gaugeReadX H r hr hL (q.1, q.2.2) s)⁻¹
        * (deepBlkY H r B hB hr hL s + gaugeReadY H r hr hL (q.1, q.2.2) s)) from by
    rw [Matrix.neg_mul, Matrix.neg_mul]]
  rw [← sub_eq_add_neg]

/-- The deepest `(2,2)`-block `deepBlkT_s = 0` at **layer 0** (`L ≥ 2`): the deepest layer-0's columns
`≥ r` vanish (`deepestPoint_layer0_cols_vanish`), and `toBlocks₂₂` reads only such columns. -/
theorem deepBlkT_layer0_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (s : Fin L) (hs : (s : ℕ) = 0) :
    (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0 := by
  funext i j
  show (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr j)) = 0
  rw [rThresholdSplit_symm_inr, rThresholdSplit_symm_inr]
  exact deepestPoint_layer0_cols_vanish H r B hB hr hL s hL2 hs _ _ (by simp)

/-- The deepest `(2,2)`-block `deepBlkT_s = 0` at **layer (L−1)** (`L ≥ 2`): the deepest layer-(L−1)'s
rows `≥ r` vanish (`deepestPoint_layerLast_rows_vanish`), and `toBlocks₂₂` reads only such rows. -/
theorem deepBlkT_layerLast_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (s : Fin L) (hs : (s : ℕ) + 1 = L) :
    (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0 := by
  funext i j
  show (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr j)) = 0
  rw [rThresholdSplit_symm_inr, rThresholdSplit_symm_inr]
  exact deepestPoint_layerLast_rows_vanish H r B hB hr hL s hL2 hs _ _ (by simp)

end DLNFibre.DLN.RLCT
