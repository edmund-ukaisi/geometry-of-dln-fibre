# Reproduction - A2 source-rank stratum measurability

Status: formalised and xhigh checked.

## Source Anchor

The source-shaped stratum used by the A2 local-measure wrappers is the set of
parameters `x` for which:

```text
finrank range(paperTotalMap W B) = r,
forall p, finrank range(Cedge x p) = rEdge p,
forall p, r <= rEdge p.
```

This note treats only measurability of that restriction set.  It does not
claim that exact-rank strata are open, and it does not construct Aoyagi's
product chart or any analytic density/loss comparison.

## Calculation

For a finite matrix `A : Matrix (Fin m) (Fin n) K` over a field, the elementary
determinantal characterization is:

```text
A.rank <= q
  iff
forall er : Fin (q+1) -> Fin m,
forall ec : Fin (q+1) -> Fin n,
  det (A.submatrix er ec) = 0.
```

The forward direction is rank monotonicity for submatrices followed by the
fact that a square matrix of rank strictly below its size has determinant zero.

For the reverse direction, assume `q+1 <= A.rank`.  Choose `q+1` independent
rows of `A`.  In the resulting `(q+1) x n` block, transpose and choose
`q+1` independent rows, equivalently independent columns of the block.  The
resulting square submatrix has independent columns, hence is a unit, hence has
nonzero determinant.  This contradicts universal vanishing of the minors.

Therefore the locus `rank(A) <= q` is an arbitrary intersection of zero loci
of continuous determinant functions, hence closed for a continuous matrix
family.  The exact-rank locus is Borel:

```text
rank = 0        iff rank <= 0,
rank = q+1      iff rank <= q+1 and not rank <= q.
```

## Source Stratum

For each edge `p`, fix finite bases of the source and target spaces and apply
the exact-rank measurability result to the coordinate matrix

```text
LinearMap.toMatrix
  (Module.finBasis K (reverseVertex W p.castSucc))
  (Module.finBasis K (reverseVertex W p.succ))
  (Cedge x p).
```

The matrix rank equals `finrank K (LinearMap.range (Cedge x p))`, by the
existing `rank_toMatrix_eq_finrank_range` bridge.  Since `Fin N` is finite, the
intersection over all edges is measurable.

The source-shaped stratum adds only two constant propositions:

```text
finrank range(paperTotalMap W B) = r,
forall p, r <= rEdge p.
```

If both are true, the source-shaped stratum is the measurable edge-rank
stratum.  If either is false, the source-shaped stratum is empty.

## Lean Landing

Lean adds the finite matrix rank bridge and Borel rank-stratum helpers in
`ChartTopology.lean`:

```text
matrix_rank_submatrix_le_rank
matrix_det_eq_zero_of_rank_lt
matrix_submatrix_det_eq_zero_of_rank_le
exists_injective_linearIndependent_matrix_rows
exists_matrix_submatrix_det_ne_zero_of_le_rank
matrix_rank_le_iff_forall_submatrix_det_eq_zero
isClosed_matrix_rank_le
measurableSet_matrix_rank_le_of_continuous
measurableSet_matrix_rank_eq_of_continuous
```

Lean adds the Aoyagi-facing wrappers in `ProductReductionBoundary.lean`:

```text
measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_continuous_finBasisMatrix
measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_continuous
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous_finBasisMatrix
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
```

## Nonclaims

- No exact-rank openness is proved.
- No local measurability is derived from a mere `ContinuousAt Cedge x0`.
- No p.13 product chart is constructed.
- No original DLN loss comparison is proved.
- No density/Jacobian transport is proved.
- No residual positivity or residual negative-power integrability is proved.
- No normal-crossing chart certificate, pole order, or RLCT conclusion is
  obtained.
