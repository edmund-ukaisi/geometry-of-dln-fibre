<task>
Lean 4 + Mathlib v4.29. I must prove the full-ambient Jacobian determinant of a per-coordinate map.

SETUP. `N : ℕ`. There is a fixed bijection `chartIdxEquiv : Fin N ≃ ChartIdx` where
`ChartIdx = Σ (k : Fin L), (Fin (schurDim k) ⊕ Fin (liftDim k))`. Each schur fiber further splits
(via `frameSplitEquiv`) into roles; one role is the "K-core" of boundary k: `Fin (t_k * t_k)`
reshaped (via `finProdFinEquiv`) to a `t_k × t_k` matrix index `(i,j)`.

The map `kLDU : (Fin N → ℝ) → (Fin N → ℝ)` is defined PER OUTPUT COORDINATE q:
  - if `chartIdxEquiv q` is a K-core slot of boundary k at matrix index (i,j):
        output = `kLens (readK x k) i j`   where `readK x k` is the t_k×t_k matrix whose (a,b) entry
        reads the input coordinate at the K-core slot (k,(a,b)) (i.e. `readK x k = matrix of those
        input coords), and `kLens : Matrix(Fin t)(Fin t) → Matrix(Fin t)(Fin t)` is a smooth lens.
  - otherwise (X/N/E roles, lift slot): output = `x q` (identity).

So kLDU acts as `kLens` on each per-boundary K-core BLOCK of coordinates, and as the identity on
every other coordinate. The blocks are DISJOINT sets of coordinates indexed by chartIdxEquiv.

ALREADY PROVED (banked):
  - `kLens_hasFDerivAt K` and `kLens_abs_det K : |det (fderiv kLens K)| = ∏_i |q_i|^{2(t-1-i)}`
    where `q = (matrixSplit K).2.1` (the per-core diagonal pivots). Single core, done.
  - `differentiable_kLDU` (kLDU differentiable everywhere).
  - `readK (kLDU x) k = kLens (readK x k)` and readX/N/E/W pass through.

GOAL: `|det (fderiv ℝ kLDU y)| = ∏_{k} ∏_{i:Fin t_k} |q_{k,i}|^{2(t_k - 1 - i)}`
(product over boundaries k of the per-core kLens dets at the K-core read at y), where
`q_{k,i} = (matrixSplit (readK y k)).2.1 i`.

The hard part: kLDU's full-ambient Jacobian is BLOCK-DIAGONAL under the chartIdxEquiv reindex —
identity blocks on spectators, a kLens-Jacobian block per K-core — and I must show its determinant
is the product of the block dets, over OPAQUE widths (t_k unknown, L unknown, schurDim/liftDim
opaque). The K-core block at boundary k depends only on the same boundary's K-core input coords
(disjoint blocks), so the global Jacobian is genuinely block-diagonal after the reindex.

I tried: conjugate by `LinearEquiv.funCongrLeft ℝ ℝ chartIdxEquiv : (Fin N → ℝ) ≃ₗ (ChartIdx → ℝ)`,
then the conjugated map is block-structured over `ChartIdx = Σ k, _`. But assembling "det of a
self-map respecting a Σ-indexed partition = product of block dets" over opaque widths looks heavy.
</task>

<output_contract>
1. The SINGLE cleanest Mathlib v4.29 route to "det of an ambient self-map that is block-diagonal
   under a fixed reindex equiv = product of block dets", for a Σ-type partition with OPAQUE block
   widths. Name the exact Mathlib lemmas (det_reindex / Matrix.det_blockDiagonal /
   LinearMap.det_pi / Equiv.Perm / toMatrix' over a reindex / det_of_upperTriangular under a linear
   order on ChartIdx). Rank 2-3 candidate routes by expected Lean pain over opaque widths.
2. Is it cheaper to AVOID the global block-det machine and instead prove the matrix
   `LinearMap.toMatrix' (fderiv kLDU y)` (or its reindex by chartIdxEquiv) is BlockTriangular w.r.t.
   some order, then `Matrix.det_of_upperTriangular`? Spell the diagonal-entry bookkeeping that would
   need: each diagonal entry is either 1 (spectator) or a kLens-Jacobian diagonal entry — but kLens
   is NOT diagonal within a core, so a pure triangular argument across the whole ambient FAILS;
   confirm or refute, and if it fails say exactly why (the within-core off-diagonal kLens entries).
3. Given (2)'s likely failure, give the cleanest "permute to block-diagonal then product" plan:
   the reindex equiv on Fin N, the Σ→Π curry, and whether `LinearMap.det_pi` over `k : Fin L`
   composed with per-k `det = (kLens block det) × (identity-spectator det = 1)` is the path. Note
   any cast/defeq landmine over the opaque widths.
4. A bounded-vs-wall verdict: is this ~150-300 line bounded over opaque widths, or does it need a
   general "block-diagonal partition det" infrastructure lemma not in Mathlib (a wall)?
</output_contract>

<grounding_rules>
Flag any lemma name you are not certain exists in Mathlib v4.29 as "VERIFY". Distinguish a route you
are confident compiles from one that is plausible-but-unverified. Do not invent lemma names.
</grounding_rules>
