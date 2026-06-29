# Reproduction - A2 Case 2 Passive Source-Chart Continuity

Date: 2026-06-29.

## Source Slice

Aoyagi pp. 10-13 use finite block coordinates in the Case 2 retained-passive
chart.  At the current Lean frontier the selected-entry residual coordinates
are already packaged as a finite map

```text
y : center -> R,
```

and the passive fields are supplied separately:

```text
A1passive, F2, A3passive, Ctop, F3.
```

The previous passive chart-produced support theorem still took a.e.
measurability of the source chart as an explicit hypothesis.  The present
calculation is the elementary topological step that makes that hypothesis
available for concrete passive product measures: if the passive fields vary
continuously in a passive parameter `theta`, then the source chart varies
continuously in `(theta, y)`.

## Claim to Formalise

Let `eta` be a topological space.  Assume the five passive field families

```text
A1passive : eta -> Fin 1 -> Matrix rho rho R
F2        : eta -> ...
A3passive : eta -> ...
Ctop      : eta -> Matrix rho rho R
F3        : eta -> ...
```

are continuous.  Then the passive selected-entry retained-passive datum

```text
(theta, y) |-> case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
  ... (A1passive theta) (F2 theta) (A3passive theta)
      (Ctop theta) (F3 theta) y eNext
```

is continuous as a map into the finite retained-passive coordinate structure.

If, in addition, the pointwise determinant-unit hypotheses hold for `Ctop` and
`A1passive`, then endpoint transport gives a continuous map into the
determinant-chart subtype, and the fixed-base retained-passive source chart

```text
(theta, y) |-> paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
  W2 B2 U0 hU0 (transportedData (theta, y))
```

is continuous.

## Calculation

The first continuity statement is coordinatewise.  The retained-passive datum
is a finite tuple

```text
(A1, F2, A3, C, Ctop, F3).
```

The passive entries `A1`, `F2`, `A3`, `Ctop`, and `F3` are continuous after
composition with `Prod.fst` by hypothesis.  The residual `C` entries depend
only on the selected-entry coordinate `y`; their continuity is the previously
banked selected-entry datum continuity composed with `Prod.snd`.  A finite
product of these coordinate maps is continuous, and the constructor
`RetainedPassiveNonredundantCoordinateData.ofTopologyTuple` is continuous.

For the source chart, the pointwise unit hypotheses place every raw datum in
the determinant chart.  The endpoint-transport map is already continuous on
the determinant-chart subtype, so the transported datum is continuous as a
subtype-valued map.  The fixed-base retained-passive source chart is already
known to be continuous on this determinant-chart subtype.  The desired source
chart is their composition.

## Dependency Boundary

The theorem should carry:

- continuity hypotheses for the five passive fields;
- pointwise unit hypotheses on `Ctop` and `A1passive` only for the source-chart
  theorem, because the determinant-chart subtype is needed there;
- the same endpoint equivalences `e` and `eNext` as the earlier passive
  source-chart statements;
- no measure hypotheses;
- no rank hypotheses.

This is a regularity theorem only.  It does not construct a passive product
measure, prove support, prove source-rank coverage, prove source-image
equality, prove determinant-chart pushforward, compute a Jacobian, transport
an original source prior, produce normal crossings, compute pole order, or
extract RLCT.

## Expected Lean Targets

```text
continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
```
