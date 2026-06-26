# Review - A2 Case 2 displayed product successor source-chart map

Date: 2026-06-26.

Reviewers: controller, with xhigh source scout `Copernicus` and xhigh
Lean/API scout `Socrates`.

## Verdict

Pass for the stated finite endpoint-reindexing scope.  The theorem turns an
entrywise successor source-chart-map readout hypothesis into a matrix identity.
It does not derive that readout from Aoyagi's paper.

## Source Check

Copernicus rechecked Aoyagi pp. 11-13 and pp. 19-22.  The paper supports the
post-pivot lower product `D_(J+1) * C'_+` on the continuing `(S,J+1)` domains
and the old selected-entry chart formula at the previous center.  It does not
identify the post-pivot product entries with fixed-base selected-center
coordinates, nor does it provide endpoint equivalences.

The successor source-chart-map theorem therefore keeps the crucial equality
as the hypothesis

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct ... i t
  = case2DisplayedSourceChartMap n hS hnext uNext residualNext ...
```

and only packages the corresponding matrix statement.

## Lean/API Check

Socrates checked that the needed equivalence is already available as
`case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs`.  Importing
`Case2ResidualIndex` into `Case2ResidualFactorProduct` is acyclic: the former
depends only on the finite Case 2 index and coordinate APIs.

The proof is entrywise:

```text
ext i t
simpa [AoyagiResidualBlockCoordinateIndex.matrix] using hentry i t
```

This belongs in `Case2ResidualFactorProduct.lean`, not in the selected-entry
measure modules, because it uses only finite matrices, the source-chart map
name, and residual-coordinate indexing.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
```

## Nonclaims

No construction of the successor source-chart readout, selected-center
readout, endpoint equivalence, `Cfac`, source-produced `Cprime`, source/image
equality, chart coverage, transition regularity, Jacobian theorem, normal
crossings, pole order, or RLCT.
