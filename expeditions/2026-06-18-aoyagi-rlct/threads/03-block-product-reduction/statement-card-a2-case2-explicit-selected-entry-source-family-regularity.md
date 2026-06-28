# Statement card - A2 Case 2 explicit selected-entry source-family regularity

## Claim

The explicit continuing Case 2 selected-entry-to-source family is a continuous
finite-coordinate map of the successor selected-entry coordinates.  Consequently
it is measurable.

## Lean Target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Target names:

```lean
continuous_case2SuccessorSelectedEntryMatrix
continuous_case2PostPivotSelectedEntryRetainedPassiveData
continuous_case2PostPivotSelectedEntryRetainedPassiveData_detChart_subtype
continuous_case2PostPivotSelectedEntrySourceEdgeFamily
measurable_case2PostPivotSelectedEntrySourceEdgeFamily
```

## Proof Basis

Each entry of the successor selected-entry matrix is a selected-entry chart-map
coordinate, hence continuous.  The constructed retained-passive datum has
constant passive fields, constant following-factor edge, and residual edge
equal to the submatrix of the successor selected-entry matrix recovered from
the zero-extension.  Therefore its product-topology tuple is continuous.

The determinant-chart subtype map is continuous by subtype construction, and
the source edge family is the composition with the existing retained-passive
`continuous_edgeMatrix_detChart_subtype` theorem.  Measurability follows from
continuity.

## Nonclaims

This does not prove source-prior pushforward, a Jacobian density comparison,
arbitrary retained-passive coverage, source-rank coverage, normal crossings,
pole order, or RLCT.

