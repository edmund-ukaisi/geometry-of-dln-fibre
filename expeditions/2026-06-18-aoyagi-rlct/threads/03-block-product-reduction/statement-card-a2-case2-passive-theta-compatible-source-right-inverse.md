# Statement Card - A2 Case 2 passive-theta compatible source right inverse

Date: 2026-06-30.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Public name:

```text
case2PassiveThetaEndpointSourceChart_readback_eq_and_rightInverse_of_sourceReadback_eq_retainedData
```

## Expected Output

For a source edge family `X` and passive-theta point `theta`, prove:

```text
case2PassiveThetaEndpointSourceChartReadback ... X = theta
and
case2PassiveThetaEndpointSourceChart ... theta = X
```

from:

```text
X in paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W2 B2 U0 hU0

sourceReadback
  (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W2 B2 U0 hU0 X)
  =
case2PassiveThetaEndpointRetainedData n hS hcont hnext theta eNext e

case2PassiveThetaEndpointInverseReadout W2 B2 n hS hnext hU0 eNext e X =
  theta.yNext
```

## Inputs Used

- `case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData`
- `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_openPartialHomeomorph.right_inv'`

## Mathematical Meaning

The theorem separates the elementary Case 2 chart algebra from the unresolved
coverage problem.  If a source point is already in the retained-passive
determinant chart, and if its recursive source readback lands in the selected
Case 2 passive-theta endpoint data with the expected selected residual readout,
then the concrete passive-theta source chart and readback are inverse on that
point.

## Nonclaims

- No source-rank coverage.
- No canonical lift through the blow-up center.
- No proof that source-rank membership gives selected-entry compatibility.
- No equality between the passive-theta image and a source-rank stratum.
- No original source-prior domination, equality, or transport.
- No determinant-chart Haar or raw-order Haar transport.
- No normal crossings, pole order, or RLCT extraction.
