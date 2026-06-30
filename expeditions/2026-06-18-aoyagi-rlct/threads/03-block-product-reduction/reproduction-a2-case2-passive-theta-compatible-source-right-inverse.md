# Reproduction - A2 Case 2 passive-theta compatible source right inverse

Date: 2026-06-30.

## Goal

Record the exact local reconstruction statement that is still elementary after
the passive-theta source-image work:

```text
readback(E) = theta and sourceChart(theta) = E
```

for a fixed source edge family `E`, provided `E` already lies in the
retained-passive determinant source chart and its retained-passive readback is
compatible with the chosen Case 2 passive-theta chart.

This is deliberately not a source-rank coverage theorem.  It is the chart-local
lifted statement supported by Aoyagi's Case 2 calculation.

## Paper calculation

Aoyagi Lemma 2 puts a matrix with a chosen regular `r x r` block in
Schur-complement coordinates:

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4,
rank(C4) = rank(A) - r.
```

The retained-passive determinant chart in Lean is the recursive version of
this calculation.  A source edge family in
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet` has determinant
minors nonzero at every recursive Schur-complement step, so `sourceReadback`
is defined on it and the retained-passive p.13 source chart is a right inverse
there.

On Aoyagi pp. 19-21, Case 2 assumes

```text
b_{J+1} = ... = b_{M(S)}
```

and no intervening tilde level, then blows up the residual matrix block along
the center `d_ij = 0`.  In the affine chart used there, the leading residual
coordinate is normalized:

```text
D_J = u_{S,J+1} D'_J,  with the (J+1,J+1) chart coordinate equal to 1.
```

Regular matrices `Q` and `P` clear the first row and column and identify the
successor residual block.  This chart is not canonical on the blow-up center:
on the exact source-rank stratum the original residual block is zero, so the
nonzero condition must be a condition on the chosen projective lift or on an
off-center nearby point.

## Lean reconstruction

Let

```text
X : forall p : Fin 2,
  reverseVertex W2 p.castSucc ->L[Real] reverseVertex W2 p.succ
```

and let

```text
E = paperEndpointFixedBaseEdgeMatrixOfReverseEdges W2 B2 U0 hU0 X
```

be its matrix form.  The compatibility hypotheses are:

```text
X in paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W2 B2 U0 hU0

sourceReadback E =
  case2PassiveThetaEndpointRetainedData n hS hcont hnext theta eNext e

case2PassiveThetaEndpointInverseReadout W2 B2 n hS hnext hU0 eNext e X =
  theta.yNext
```

The second hypothesis says that the retained-passive determinant coordinates
read from the source edge family are exactly the endpoint-transported retained
data of the chosen Case 2 passive-theta coordinate.  The third hypothesis says
that the selected-entry inverse readout chooses the same residual affine
coordinate `yNext`.

Then the concrete passive-theta readback recovers `theta` by definition:

```text
case2PassiveThetaEndpointSourceChartReadback ... X = theta.
```

For the other direction, the retained-passive right inverse gives

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData ...
  (sourceReadback E) = X.
```

Substituting the compatibility equality identifies the left-hand side with

```text
case2PassiveThetaEndpointSourceChart ... theta.
```

Therefore:

```text
case2PassiveThetaEndpointSourceChart ... theta = X.
```

## Boundary

This proves reconstruction only under determinant-chart membership and the
two compatibility hypotheses above.  It does not prove:

- that source-rank membership implies determinant-chart membership;
- that source-rank membership implies selected-entry/pivot compatibility;
- that one passive-theta endpoint chart covers a source-rank neighborhood;
- source-prior domination or transport;
- determinant-chart Haar transport, raw-order Haar transport, normal
  crossings, pole order, or RLCT extraction.

