# Statement Card - A2 Case 2 Selected-Entry Passive-Parameter Datum

Status: sorry-free focused build; reviewed.

Reproduction:

```text
reproduction-a2-case2-selected-entry-passive-parameter-datum.md
```

Review:

```text
review-a2-case2-selected-entry-passive-parameter-datum.md
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

## Claim

The Case 2 selected-entry retained-passive datum can be enlarged by supplying
the retained passive coordinates independently while preserving the existing
selected-entry residual readout.  Determinant-chart membership is obtained from
the supplied unit hypotheses on `Ctop` and `A1passive`.

## Lean

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_detChart
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

## Gloss

Given the same successor selected-entry residual coordinates used by the
reduced Case 2 datum, and arbitrary passive retained fields
`A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`, Lean constructs a
`RetainedPassiveNonredundantCoordinateData` whose residual `C` field is the
selected-entry residual family.  If `Ctop.det` and every `A1passive p.det` are
units, then the datum and its endpoint transport lie in the retained-passive
determinant chart.  After endpoint transport, the residual factor product is
the same selected-entry center-coordinate chart matrix as in the reduced
datum.

## Proved

- The passive-parameter datum exists as a finite retained-passive coordinate
  object.
- Under explicit `Ctop` and `A1passive` determinant-unit hypotheses, it lies in
  the retained-passive determinant chart.
- Endpoint transport preserves that determinant-chart proof.
- The endpoint-transported residual factor product is independent of the
  supplied passive variables and agrees with the successor selected-entry
  center-coordinate chart matrix.

## Assumed

- The finite index and decidable equality hypotheses required by the matrix
  and retained-passive APIs.
- The Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- The supplied determinant-unit hypotheses on `Ctop` and `A1passive`.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive block substitutions and the
p.13 product-difference display.  The Lean proof itself is finite coordinate
algebra and uses no analytic citation.

## Deferred

- A passive-coordinate source map.
- A local inverse or image/coverage theorem.
- A determinant-chart or raw-Haar measure pushforward from the selected-entry
  passive chart.
- External/original source-prior transport and Jacobian density comparison.
- Normal crossings, pole order, and RLCT extraction.

## Route

Keep the old selected-entry construction for the residual `C` family and
replace only the passive fields by supplied parameters.  The determinant-chart
proof unfolds to the `Ctop` and `A1passive` unit hypotheses.  The residual
readout unfolds the new datum and reuses the existing reduced selected-entry
residual-factor theorem, since the `C` field is unchanged.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
```

Warnings were replayed from imported
`ProductReductionStepRegularDensity.lean`, not introduced by this card's
declarations.

## Nonclaims

This card does not prove source-rank coverage, selected-entry image coverage,
the determinant-chart pushforward
`m.restrict Sdet = Measure.map chart weightedBox`, full raw-Haar transport,
source-prior transport, normal crossings, pole order, or RLCT.
