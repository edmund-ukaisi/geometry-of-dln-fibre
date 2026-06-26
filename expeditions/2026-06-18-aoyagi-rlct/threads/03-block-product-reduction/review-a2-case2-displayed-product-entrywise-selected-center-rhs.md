# Review - A2 Case 2 displayed product entrywise selected-center RHS

Date: 2026-06-26.

Reviewers: controller, with xhigh source scout `Mill` and xhigh Lean/API scout
`Turing`.

## Verdict

Pass for the stated finite matrix-extensionality scope.  The theorem does not
prove the selected-center readout; it only turns an entrywise readout
hypothesis into the submatrix RHS needed by the existing residual-factor
bridge.

## Source Check

Mill rechecked Aoyagi pp. 11-13 and pp. 19-22.  The paper supports the
post-pivot lower product `D_{J+1} * C'_+` on the continuing `(S,J+1)` residual
domains.  It does not provide a canonical selected-center coordinate matrix,
endpoint equivalences, or `residualCoordEquiv` for the fixed-base readout.

The correct source-faithful boundary is therefore an entrywise hypothesis:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct ... i t
  = centerCoord (residualCoordEquiv (e2 i, e0 t)).
```

## Lean/API Check

Turing confirmed that the generic helper belongs in
`Case2ResidualFactorProduct.lean`, because it only depends on finite product
and residual-coordinate APIs.  A future specialization with
`SelectedEntrySignedBox.CenterCoord.chartMap pivot y` should live downstream,
not in this module, to avoid importing selected-entry measure/chart material
into the finite bridge layer.

The proof is entrywise:

```text
ext i t
simpa [AoyagiResidualBlockCoordinateIndex.matrix] using hentry i t
```

The composed theorem then delegates to the previous selected-center matrix
bridge.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
```

## Nonclaims

No construction of the entrywise readout, `Cfac`, endpoint equivalences,
`Cprime`, source/image equality, chart coverage, transition regularity,
Jacobian theorem, normal crossings, pole order, or RLCT.
