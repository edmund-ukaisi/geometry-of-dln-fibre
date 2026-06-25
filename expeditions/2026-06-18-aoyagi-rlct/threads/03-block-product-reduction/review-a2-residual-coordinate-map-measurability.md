# Review - A2 residual-coordinate map measurability

Date: 2026-06-25.

Reviewer: xhigh subagent Herschel the 5th.

Scope:

```text
lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

## Findings

No blocking issues found.

## Checks

The reviewer confirmed:

- `measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix`
  assumes measurability of the exact fixed-base edge-matrix family, rebuilds
  that same `E`, runs the deterministic suffix recursion, and projects the
  final `D` block.
- The theorem does not infer measurability from `Cedge` as a
  continuous-linear-map-valued function.
- The suffix-state measurability lemmas use finite real matrix operations and
  global Borel measurability of totalized real matrix inverse, avoiding any
  determinant-chart or source-rank hypothesis.
- The local-measure wrapper only derives residual positive-set measurability
  through the measurable residual coordinate map, while preserving the signed
  box, pushforward, monomial lower-bound, and density hypotheses.

## Residual Assumptions

Fixed-basis edge-matrix measurability remains an explicit finite-coordinate
hypothesis.  No determinant chart, source-rank openness, analytic chart,
Jacobian, normal-crossing, pole order, or RLCT result is included in this
slice.

## Verdict

Approved.
