<task>
Lean 4 + Mathlib v4.29. I need the cleanest proof that a specific "arrow" matrix has determinant
`(x p)^(active.card - 1)`. Give me the proof STRATEGY (which Mathlib lemmas, what order), not a full
script — I write/run the Lean. Be concrete about lemma names you're confident exist in v4.29.

## The matrix
`M : Matrix (Fin N) (Fin N) ℝ` is the standard-basis matrix of a continuous linear map
`pivotBlowupOnDeriv active p x` on `Fin N → ℝ`, where `active : Finset (Fin N)`, `p ∈ active`.
Entry formula (already proven, call it `pbon_entry`):
  M i j =
    if i = p then (if j = p then 1 else 0)                       -- pivot row = e_p
    else if i ∈ active then (x p)·(if j = i then 1 else 0) + (x i)·(if j = p then 1 else 0)  -- active row
    else (if j = i then 1 else 0)                                -- spectator row = e_i

So: diagonal is `1` at p, `x p` at active\{p}, `1` at spectators. The ONLY off-diagonal nonzero
entries are in COLUMN p: `M i p = x i` for active `i ≠ p`. (An "arrow"/"claw" matrix: diagonal +
one column.) NOT lower/upper triangular in the `Fin N` order (column-p off-diagonal entries sit both
above and below the diagonal, since active indices can be `< p` or `> p`).

## The target
`M.det = (x p) ^ (active.card - 1)`  (sympy-confirmed for several active sets/pivots).
Reason: it's diagonal except column p; the column-p off-diagonal entries `x i` (rows i ∈ active\{p})
can be cleared by column ops (subtract `(x i)/(x p) ·` column i from column p — each active column i
has its sole nonzero in row i = `x p`), leaving a diagonal matrix with product `1 · (x p)^(active.card-1) · 1^spectators`.
But that needs `x p ≠ 0` for the division, whereas I want the identity for ALL x (the det is a
polynomial identity, true even at x p = 0 where both sides are 0 if active.card ≥ 2).

## Candidate routes I'm weighing (rank them, pick the cleanest for an ALL-x polynomial identity)
(a) Permutation/reindex to make it lower-triangular: conjugate by an equiv `e : Fin N ≃ Fin N`
    putting `p` first, then `Matrix.det_of_lowerTriangular`, via `det_submatrix_equiv_self` /
    `det_reindex_self`. Concern: ordering `active` and building `e` is fiddly.
(b) Clear column p by `det` column-operation lemmas that hold for ALL entries (no division):
    `Matrix.det_updateColumn_add` / `det_updateColumn_smul` / `det_updateColumn_add_self` style —
    express column p as (e_p basis col) + Σ_{active i≠p} (x i)·(col that's `x p · e_i`)... but the
    cols aren't scalar multiples cleanly. Concern: the column-clear needs `1/x p`, killing the
    all-x property.
(c) Cofactor expansion along column p (`Matrix.det_succ_column` / Laplace) — but `Fin N` general,
    and the arrow structure should make most cofactors vanish. Concern: messy for general N.
(d) Direct `Matrix.det_apply` (sum over permutations): only the identity permutation and the
    transpositions/cycles touching p survive? Concern: combinatorial.
(e) Recognize M = (identity on spectators) ⊕ (arrow on active block) and use a block-det lemma
    (`Matrix.det_fromBlocks_zero₁₂` / `det_fromBlocks_zero₂₁`) after reindexing active to a prefix —
    then the active block is exactly the #58 all-active arrow whose det I already proved
    (`pivotBlowupDeriv_det = (x 0)^n`, lower-triangular after p→0).

I have a PROVEN all-active version: for `pivotBlowup` (pivot 0, all coords active) on `Fin (n+1)→ℝ`,
`det = (x 0)^n` via toMatrix' + `BlockTriangular toDual` + diagonal product. So route (e) — reduce
the subset/spectator case to that proven block — is appealing if the block-diagonal + reindex
plumbing is clean.

## Output
Rank (a)-(e) for THIS all-x polynomial identity. For the top pick: the exact Mathlib lemma sequence
(names you're confident exist in v4.29; mark any "unverified — grep"), and the one tricky step. If
(e), say exactly how to get the block-diagonal form (which equiv, which fromBlocks det lemma) and
whether reusing my proven all-active det is realistic or if re-proving in-place is simpler. ≤ 1 short
signature per lemma; no long code.
</task>

<output_contract>
A ranked list (a)-(e) with one-line reason each, then a "TOP PICK" section: the lemma sequence (≤8
steps), the single trickiest step, and confidence flags on lemma names. Terse.
</output_contract>

<grounding_rules>
Mark each lemma name as "confident (v4.29)" or "unverified — grep". Do not invent names. If the
all-x polynomial-identity requirement makes a route unsound (e.g. needs division by x p), say so
explicitly rather than hand-waving.
</grounding_rules>
