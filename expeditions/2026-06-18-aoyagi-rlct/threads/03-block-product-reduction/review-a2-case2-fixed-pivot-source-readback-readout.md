# Review - A2 Case 2 fixed-pivot source-readback readout

Reviewer: xhigh read-only checker `Faraday`.

Verdict: PASS.

The theorem shape is sound.  The endpoint orientation is correct: the row
equivalence is `(e (Fin.last 2)).symm`, and the column equivalence is
`((e 0).symm.trans eNext)`, matching
`case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs`.

The pointwise entry theorem correctly evaluates the existing selected-entry
matrix identity at `residualCoordEquiv.symm pivotNext`.  The `value_matrix`
API supplies the entry equality, the endpoint inverse law reduces
`residualCoordEquiv (residualCoordEquiv.symm pivotNext)` to `pivotNext`, and
`SelectedEntrySignedBox.CenterCoord.chartMap_pivot` gives the final
`yNext pivotNext`.

The fixed-base source-readback lift follows from
`sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData`,
which rewrites the fixed-base source readback to the endpoint-transported
datum before applying the datum-level pointwise theorem.

Nonclaims checked: no construction of `tau`, no proof of `hTau`, no canonical
endpoint labelling, no selected-entry label-preservation theorem for arbitrary
noncanonical endpoint equivalences, no arbitrary `ofTopologyTuple` alignment,
no source-prior transport, no Jacobian comparison, no normal crossings, no
pole order, and no RLCT.
