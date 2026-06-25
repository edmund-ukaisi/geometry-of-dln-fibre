# Review - A2 residual-factor product rank obstruction

Date: 2026-06-25.

Reviewer: xhigh Lean/API scout Singer.

## Verdict

The rank-obstruction lemmas are mathematically sound and appropriately scoped
for the Aoyagi-only expedition.

## Checked Statements

```text
ChartLocalSuffixState.residualFactorProduct_trans
ChartLocalSuffixState.rank_residualFactorProduct_le_card_intermediate
```

The split law is correctly stated for `residualFactorProduct C`, and the rank
bound correctly follows over a nontrivial commutative ring from
`Matrix.rank_mul_le_left` and `Matrix.rank_le_card_width`.

## Boundary Notes

Keep the split/rank obstruction on explicit residual factors, not on bare
`residualProduct E`: the raw `residualBlock E j p` depends on the top endpoint
`j`, so a naive split

```text
residualProduct E j i = residualProduct E j q * residualProduct E q i
```

would overclaim.  To use the obstruction for a residual product, first pass
through explicit factors using the existing factor-product bridge or
product-coordinate hypotheses.

The rank lemma proves only factor-through-intermediate-space obstruction.  It
does not prove exact rank, source-rank openness, residual block rank formulas,
selected-entry matrix factorization, source chart construction, normal
crossings, pole order, or RLCT.  If later translated to Aoyagi widths, the
cardinality `Fintype.card (kappa q)` must be separately connected to the
relevant complement width.
