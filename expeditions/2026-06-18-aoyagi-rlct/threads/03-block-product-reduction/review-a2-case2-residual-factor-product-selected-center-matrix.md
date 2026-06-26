# Review - A2 Case 2 residual-factor product selected-center matrix

Date: 2026-06-25.

Reviewer: controller, using xhigh bridge scout `Hypatia`.

## Verdict

Pass for the stated finite matrix bridge.  The theorem does not prove the
displayed selected-center RHS; it only removes the final equivalence-submatrix
wrapper once that RHS is supplied.

## Checks

- Hypatia confirmed that Aoyagi pp. 19-22 support the post-pivot lower product
  `D_{J+1} * C'_+`, reindexed to the continuing `(S,J+1)` residual block.
- The proof uses the already-landed
  `case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix`.
- `Matrix.eq_of_submatrix_equiv_eq` is entrywise: evaluate the submatrix
  equality at inverse images of the target row and column.
- The theorem deliberately takes a generic `centerCoord : center -> R`; the
  selected-entry chart specialization can instantiate this with
  `SelectedEntrySignedBox.CenterCoord.chartMap pivot y` downstream without
  importing signed-box analytic material into this finite bridge module.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
```

## Nonclaims

No construction of `Cfac`, endpoint equivalences, `Cprime`, source/image
equality, chart coverage, transition regularity, Jacobian theorem, normal
crossings, pole order, or RLCT.
