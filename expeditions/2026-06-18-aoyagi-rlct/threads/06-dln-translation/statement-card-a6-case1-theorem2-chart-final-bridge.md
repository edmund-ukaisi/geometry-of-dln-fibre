# Statement card - A6 Case 1 chart-final boundary bridge

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Case1Theorem2ChartFinalBridge.lean`

Name:

- `Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`

## Claim

A supplied selected-old Case 1/A0 coordinate bridge can fill
`AoyagiTheorem2SuppliedChartFinalBoundary` once the following are supplied:

- selected-width provenance
  `m = aoyagiSelectedReducedWidths H r cuts`;
- the chart-level extraction hypothesis;
- a candidate-ratio/Theorem 2 lambda equality;
- a global active-ratio lower bound by the Case 1 candidate ratio;
- chart-count equality and an all-chart upper bound at that same candidate
  ratio.

## Inputs Kept Explicit

- supplied selected-old Case 1 source-boundary provenance through `B`;
- supplied chart certificate `Cnc`;
- supplied coordinate `p` and chart `c`;
- supplied selected-width provenance;
- supplied A0 extraction hypothesis;
- supplied finite lower-bound and chart-count facts.

## Proved

The theorem constructs:

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  Cnc Lthm ell H r cuts m data lambda poleOrder.
```

## Not Proved

No chart certificate construction, no selected-old chart/source production,
no chart coverage, no finite lower-bound proof, no chart-count proof, no
selected-width provenance proof, no analytic extraction theorem, no pole
order, and no RLCT.

## Verification

Initial focused check passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case1Theorem2ChartFinalBridge
```

Independent xhigh review passed:
`review-case1-theorem2-chart-final-bridge-a6.md`.

Focused and full checkpoint gates passed and are recorded in the review
artifact.
