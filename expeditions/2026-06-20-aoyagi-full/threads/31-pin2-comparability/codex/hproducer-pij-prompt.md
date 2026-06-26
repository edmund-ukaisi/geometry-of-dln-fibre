<task>
I am filling the last gap (`hproducer`) of a Lean proof in a DLN-fibre/RLCT formalisation.
I need you to ADJUDICATE one load-bearing matrix-identity truth-value and rank the
decomposition. NO Lean syntax needed — pure linear algebra + exact reasoning.

## SETUP (L = 2 deep linear network, rank-r reduced core, widths H0, H1=H(mid), H2=H_last)

Objects (all real matrices):
- `symm w` is a per-layer tuple of matrices `A_s = (paramsEquivFlat.symm w)_s`, s = 0,1.
  `prod(symm w) := A_1 · A_0` (the L=2 matrix product, an H0×H2 matrix). [composable tuple]
- `B` is the fixed target, rank r, an H0×H2 matrix.
- `P0` (H0×H0), `QL` (H2×H2) are the FIXED endpoint frames (units), independent of w.
- `J : Fin r ↪ Fin H2` is B's pivot column set (sorted). `J` need NOT be the front columns {0..r-1}.
- `rThr := rThresholdSplit r n` is the equiv `Fin n ≃ Fin r ⊕ Fin (n-r)` splitting off the FIRST r.
- `pivotThr J := pivotThresholdSplit r H2 J` is the equiv `Fin H2 ≃ Fin r ⊕ Fin (H2-r)` whose
  LEFT block enumerates the (sorted) pivot columns `range J`, right block the sorted complement.
- For a matrix M, `reindex eRow eCol M` is the relabelled matrix `M' (i,j) = M (eRow.symm i) (eCol.symm j)`,
  then `toBlocks₁₁/₁₂/₂₁/₂₂` are the 4 blocks under the `r ⊕ (n-r)` split.

The framed reconstruction `framedParamsPivot(split w)` is a per-layer tuple `F_s`:
- For the NON-last layer (s=0): `F_0 = P_0frame · A_0 · Q_0frame` EXACTLY (banked, "hS1": clean round-trip).
- For the LAST layer (s=1): `framedParamsPivot_last` gives
    `F_1 = reindex(rThr.symm, (pivotThr J).symm)(fromBlocks 1 0 0 0)`              [the "corner"]
         + Pf_1 · reindex(rThr.symm, (pivotThr J).symm)(fromBlocks readX readY readZ coreRead) · Qf_1
  where the READS (readX/readY/readZ/coreRead) are J-INDEPENDENT THRESHOLD-column decodes:
  block-col `inl q ↦` deviation column `q`, block-col `inr q ↦` deviation column `r+q`.
  RESULT (pen-and-paper + a prior decorrelated Codex, ALREADY ESTABLISHED in this thread):
    `F_1 = Pf_1 · deepest_1 · Qf_1  +  Pf_1 · colPerm_J( (symm(w - w0))_1 ) · Qf_1`
  where `colPerm_J(M)(i,j) = M(i, π_J(j))`, `π_J(j) := rThr.symm( pivotThr(J)( j ) )` is a column
  PERMUTATION (NOT identity unless J is the front pivot). The clean form `F_1 = Pf_1·A_1·Qf_1` is FALSE.
  i.e. `colPerm_J(M) = M · Pπ` for an orthogonal permutation matrix `Pπ` (column permutation by π_J).

The telescope (banked `endpoint_telescoping_eq`) gives, when every layer is `F_s = P_s·A_s·Q_s`:
  `prod(F) = P0 · prod(A) · QL`     (P0 = endpoint cast of Pf_0, QL = endpoint cast of Qf_1).
But on the last layer F_1 carries the colPerm π_J, so for general w:
  `prod(framedParamsPivot(split w)) = P0 · ( colPerm_J(A_1) · A_0 ) · QL`
  = `P0 · ( A_1 · Pπ · A_0' )...` — wait, careful: colPerm acts on A_1's COLUMNS (H2 side, the OUTPUT/last side).
  Since `prod = A_1 · A_0` for L=2 and A_1 is H(mid)×H2? NO — composable: A_0 is H0×Hmid... let me restate:
  composable tuple `A_s : Fin(H s.castSucc) → Fin(H s.succ)`, prod = A_0 (first) then ... the product is
  `prod H A = A_0 * A_1 * ... ` left-to-right? The repo's `prod` is the ordered matrix product of the tuple.
  The LAST layer's colPerm permutes the FINAL output columns (the H2 = H_last side), i.e. it right-multiplies
  the whole product by Pπ: `prod(framedParamsPivot(split w)) = P0 · prod(symm w) · (Pπ_lifted) · QL`-ish,
  where Pπ is the H2×H2 column permutation. [VERIFY this placement.]

## THE CONSUMER (what I actually need)

`deepestEFull(split w)` reads the residual blocks `(M_full.toBlocks₁₁ − 1, M_full.toBlocks₁₂, M_full.toBlocks₂₁)`
of `M_full := reindex(rThr, pivotThr J)( prod(framedParamsPivot(split w)) )`.

`hconj` (a conjunct I get to satisfy by CHOOSING the blocks P00,P01,P10,P11) sets them = the toBlocks of
`M_conj := reindex(rThr, pivotThr J)( P0 · (prod(symm w) − B) · QL )`.

I must prove conjunct (b): `∑ deepestEFull(split w)² = ∑(P00−1)² + ∑P01² + ∑P10²`, i.e. the residual
blocks of `M_full` have the SAME (P00−1,P01,P10) entries (or at least equal Frobenius energy) as the
residual blocks of `M_conj`. The B-normalization (banked hS3b) gives
`reindex(rThr, pivotThr J)(P0·B·QL) = fromBlocks 1 0 0 0` (the corner), so dropping B shifts toBlocks₁₁ by +1.

So conjunct (b) reduces to:  M_full = M_conj + (fromBlocks 1 0 0 0)  on the RESIDUAL blocks (₁₁−1, ₁₂, ₂₁),
i.e. M_full and reindex(rThr,pivotThr J)(P0·prod(symm w)·QL) have the SAME residual blocks.

## THE QUESTION (adjudicate, exact)

Q1. With the colPerm π_J on the last (H2/output) layer, is it TRUE that
      `reindex(rThr, pivotThr J)( prod(framedParamsPivot(split w)) )`
      `= reindex(rThr, pivotThr J)( P0 · prod(symm w) · QL )`  (on the residual blocks, or exactly)?
    The claim of "verdict option A" is: the OUTER `reindex(rThr, pivotThr J)` (same on M_full and M_conj)
    ABSORBS the column permutation Pπ, because Pπ permutes EXACTLY the columns that pivotThr(J) is sorting,
    so the right-reindex by `pivotThr J` undoes the column permutation π_J. Is that correct? Precisely:
    `π_J(j) = rThr.symm(pivotThr(J)(j))`. The colPerm by π_J followed by reindexing columns by `pivotThr J`
    (i.e. column j of the result reads source column `pivotThr(J).symm(j)`)... compose the two column maps.
    Does `(reindex(rThr, pivotThr J)) ∘ (colPerm π_J)` equal `(reindex(rThr, rThr))` (the THRESHOLD reindex,
    no pivot)? Work out the exact column-index composition and state whether the residual blocks coincide.

Q2. If Q1 is NOT a clean identity (residual blocks differ as matrices), is the WEAKER Frobenius-energy
    equality `∑(M_full residual)² = ∑(M_conj residual)²` still TRUE? (A column permutation preserves the
    SET of column-energies, but the r⊕(H2−r) BLOCK SPLIT could move a column between the P0x and P1x blocks.
    Does π_J map pivot columns to {0..r-1} exactly, so the block partition is preserved? If yes, energy is
    preserved even if entries are permuted within a block.)

Q3. Given Q1/Q2, what is the CLEANEST way to state conjunct (b) so it is PROVABLE, and is the colPerm
    a genuine obstruction or a notational artifact that cancels? Rank: (i) clean entrywise identity,
    (ii) energy-only, (iii) genuinely needs new lemmas. Give the exact column-index algebra for your verdict.
</task>

<output_contract>
1. VERDICT on Q1 (TRUE/FALSE + the exact column-index composition `pivotThr(J).symm ∘ (rThr ∘ π_J)` or
   equivalent — show the cancellation or the residue explicitly).
2. VERDICT on Q2 (does the block partition survive π_J; is energy preserved).
3. The cleanest provable form of conjunct (b) + whether it needs new lemmas (rank i/ii/iii).
4. Flag every step that is INFERENCE vs a fact you can derive from the index definitions given.
Keep it under ~500 words. Exact algebra, no Lean.
</output_contract>

<grounding_rules>
You are reasoning from the index definitions I gave (rThr splits off first r; pivotThr J sorts pivot
columns to the left block; π_J = rThr.symm ∘ pivotThr J). Derive the composition exactly. If a step
depends on an assumption I did not state (e.g. how `prod` orders the tuple, or whether colPerm is on
rows vs columns), FLAG it as an assumption and give the verdict conditional on it. Do not assert the
cancellation works without showing the index algebra.
</grounding_rules>
