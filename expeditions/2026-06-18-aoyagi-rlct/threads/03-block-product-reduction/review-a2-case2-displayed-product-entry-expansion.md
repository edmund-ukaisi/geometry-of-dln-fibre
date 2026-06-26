# Review - A2 Case 2 displayed product entry expansion

Date: 2026-06-26.

Reviewers: controller, using the prior xhigh Case 2 source audits.

## Verdict

Pass for finite matrix-product expansion.  The theorem is a definitional
entrywise view of the displayed post-pivot lower product and does not move any
source/chart readout boundary.

## Source Check

Aoyagi pp. 19-22 support the continuing Case 2 lower product
`D_(J+1) * C'_+` after the selected pivot row and column are separated.  The
intermediate summation index is the successor residual-column domain
`Case2ResidualColIndex n S (J+1)`.

The theorem does not read entries of this product as raw chart variables.  In
particular, it does not identify

```text
sum_j D_(J+1)(i,j) * C'_+(j,t)
```

with either a selected-center coordinate or a successor source-chart
coordinate.

## Lean/API Check

The theorem unfolds
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct` and uses
`Matrix.mul_apply`:

```text
simp [case2DisplayedPostPivotFreeTwoEdgeFactorProduct, Matrix.mul_apply]
```

The required finite intermediate domain is already available for
`Case2ResidualColIndex n S (J+1)`.

The direct free-`Cprime` version additionally unfolds
`case2DisplayedPostPivotFreeFollowingFactor` and
`case2DisplayedFreeCprimeTail`.  It is still finite reindexing only.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
```

## Nonclaims

No selected-center readout, successor source-chart readout, endpoint
equivalence, compatible residual factors, source-produced `Cprime`,
source/image equality, chart coverage, transition regularity, Jacobian
theorem, normal crossings, pole order, or RLCT.
