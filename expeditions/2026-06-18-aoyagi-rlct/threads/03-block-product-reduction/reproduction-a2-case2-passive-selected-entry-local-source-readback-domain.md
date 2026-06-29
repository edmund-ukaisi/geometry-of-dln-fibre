# Reproduction - A2 Case 2 Passive Selected-Entry Local Source-Readback Domain

Date: 2026-06-29.

Status: controller reproduction before Lean formalisation.  This is finite
retained-passive source-coordinate bookkeeping, not source-prior or measure
transport.

## Source Slice

Aoyagi pp. 10-13 use the retained-passive block variables obtained by the
elementary substitutions

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C  = -A3 A1^{-1} A2 + A4.
```

In the product step, the p.13 product-difference display separates the regular
variables from the residual product:

```text
[ C1 - I   -F2
  -F3      prod C^(s) - F3 F2 ].
```

For the current Case 2 selected-entry frontier, the selected-entry coordinates
only supply the residual `C` family.  The retained passive coordinates

```text
A1passive, F2, A3passive, Ctop, F3
```

must remain independent parameters if the source chart is meant to remember
the full p.13 coordinate datum rather than the reduced section where these
fields are fixed.

## Coordinate Calculation

Fix a passive parameter `theta` and selected-entry residual coordinates
`y : center -> R`.  The passive selected-entry retained datum is

```text
rawData(theta, y) =
  case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    ... (A1passive theta) (F2 theta) (A3passive theta)
        (Ctop theta) (F3 theta) y eNext.
```

After endpoint transport by `e`, set

```text
data(theta, y) = endpointTransport e (rawData(theta, y)).
```

The determinant-chart condition for `data(theta, y)` is exactly:

```text
IsUnit ((Ctop theta).det)
and
forall p : Fin 1, IsUnit ((A1passive theta p).det).
```

No selected-entry coordinate enters this determinant condition.  The
selected-entry coordinates affect only the stored residual factors `C`.

Let

```text
Y(theta, y) = topologyTuple (data(theta, y)).
```

If the passive fields are continuous in `theta`, then `rawData` is continuous
in `(theta, y)`.  Endpoint transport and `topologyTuple` are continuous, so
`Y` is continuous.  Since the retained-passive determinant chart is open and
the base point `z0 = (theta0, y0)` satisfies the two unit hypotheses above,

```text
U = Y^{-1}(topologyTupleDetChartSet)
```

is an open neighborhood of `z0`.  For every `z in U`, the transported datum
`data z` is in the determinant chart.

## Source-Readback Calculation

For `z in U`, define the fixed-base p.13 source edge family

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (data z).
```

The fixed-base matrix extraction theorem gives

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges
  W2 B2 U0 hU0 sourceChart(z)
  = (data z).edgeMatrix.
```

Because `data z` is in the determinant chart, the retained-passive
source-readback inverse theorem applies:

```text
sourceReadback ((data z).edgeMatrix) = data z.
```

Combining the two equalities gives the desired full readback statement:

```text
sourceReadback
  (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W2 B2 U0 hU0 sourceChart(z))
  = data z.
```

The same determinant-chart proof also shows `sourceChart z` lies in the named
retained-passive p.13 local source.  This is pointwise source-coordinate
membership and inverse/readback, not an image equality for all nearby source
points.

## Lean Target

The target theorem should produce an explicit open set:

```text
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
```

It should assume:

- continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`;
- basepoint determinant units for `Ctop z0.1` and `A1passive z0.1`;
- the endpoint equivalences `e` and `eNext`;
- the fixed-base complement data `U0, hU0`.

It should prove:

- `IsOpen U`;
- `z0 in U`;
- for every `z in U`, `sourceChart z` is in the retained-passive p.13 local
  source;
- for every `z in U`, source readback of the extracted edge matrices equals
  the full transported retained-passive datum `data z`.

## Nonclaims

This theorem does not prove selected-entry source-image equality, coverage of
arbitrary source points, source-rank coverage, determinant-chart Haar
pushforward, raw-Haar transport, source-prior transport, Jacobian
change-of-variables, exact localized residual marginal, normal crossings, pole
order, or RLCT extraction.
