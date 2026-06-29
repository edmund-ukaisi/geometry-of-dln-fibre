# Review - A2 Case 2 produced local-source point readout

Reviewer: xhigh read-only checker `Russell the 2nd`.

Verdict: PASS.

## Findings

None.

The new theorem is a narrow point-production package.  It produces selected
coordinates `yNext`, proves `yNext pivotNext != 0`, proves that the
endpoint-transported Case 2 source edge family lies in the retained-passive
p.13 local source, and proves exact residual-coordinate readout against the
target selected-entry value.

The proof uses the fixed-pivot inverse
`SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero`.  Local-source
membership comes from
`retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData`,
and the residual-coordinate readout delegates to
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero`.

## Boundary

The theorem does not state source-rank-stratum membership, selected-entry
source-rank coverage, source/image equality, source-prior or measure
transport, Jacobian comparison, analytic atlas construction, normal crossings,
pole order, or RLCT.

## Verification

Controller verification:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
lean/scripts/sorries
git diff --check
```

The focused build passed.  The only warnings were replayed from the existing
dependency `ProductReductionStepRegularDensity`.  `lean/scripts/sorries`
reported no forbidden declarations or exits, and the touched-Lean-file
forbidden-marker scan was clean.
