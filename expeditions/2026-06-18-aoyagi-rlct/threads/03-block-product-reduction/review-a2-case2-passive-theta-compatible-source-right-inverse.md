# Review - A2 Case 2 passive-theta compatible source right inverse

Date: 2026-06-30.

Reviewer: xhigh read-only checker `Confucius`.

## Verdict

PASS after documentation correction.

## Check

The Lean theorem is genuinely compatibility-gated.  It assumes:

```text
X in paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W2 B2 U0 hU0
sourceReadback(edgeMatrixOfReverseEdges X) =
  case2PassiveThetaEndpointRetainedData ... theta eNext e
case2PassiveThetaEndpointInverseReadout ... X = theta.yNext
```

before concluding:

```text
case2PassiveThetaEndpointSourceChartReadback ... X = theta
case2PassiveThetaEndpointSourceChart ... theta = X
```

The second conjunct is the retained-passive determinant source-chart right
inverse rewritten by the `sourceReadback` compatibility equality.  It is not
source-rank coverage, source-image equality, source-prior transport, Haar
transport, normal crossings, pole order, or RLCT extraction.

## Correction Applied

The original statement card listed
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph.right_inv`
as the right-inverse input.  The proof actually uses the ambient open partial
homeomorphism:

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_openPartialHomeomorph.right_inv'
```

The statement card has been corrected accordingly.

