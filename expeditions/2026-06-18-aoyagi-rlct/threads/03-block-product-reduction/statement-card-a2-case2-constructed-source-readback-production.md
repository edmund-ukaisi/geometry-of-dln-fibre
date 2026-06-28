# Statement card - A2 Case 2 constructed source-readback production

## Claim

For the continuing Case 2 branch, successor selected-entry coordinates with
nonzero displayed successor pivot coordinate determine a constructed two-edge
retained-passive-shaped source family `E` in the source-recursive determinant
chart.  The actual `sourceReadback E` residual-factor product is exactly the
successor selected-entry matrix, and hence is nonzero.

This is constructed source production. It is not arbitrary retained-passive
coverage.

## Lean Artifacts

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

New names:

```lean
exists_sourceRecursive_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
exists_sourceRecursiveEdgeFamily_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
```

## Proof Basis

The finite displayed-product source construction gives `residual` and
`Cprime` whose displayed Case 2 product is the successor selected-entry
matrix.  These factors are packaged as
`case2PostPivotRetainedPassiveData`.

The source family is the retained-passive source map `data.edgeMatrix`.
Existing source/readback infrastructure proves:

```text
sourceRecursiveDetChart data.edgeMatrix
sourceReadback data.edgeMatrix = data.
```

Rewriting the `sourceReadback` residual factors to `data.C` and unfolding the
synthetic Case 2 data identifies the residual-factor product with the
successor selected-entry matrix.

## Nonclaims

This does not prove the same statement for arbitrary retained-passive
`sourceReadback E`. It does not prove selected-entry source/prior measure
transport, original source-rank coverage, normal crossings, pole order, or
RLCT.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` and full
`DLNFibre` build passed with only pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, changed-Lean-file forbidden-marker search, direct
axiom-footprint audit, and xhigh implementation review by `Boole` passed.  The
new endpoints report `[propext, Classical.choice, Quot.sound]`.
