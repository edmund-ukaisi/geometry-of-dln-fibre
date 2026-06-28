# Reproduction - A2 retained-passive selected-entry determinant-chart residual handoff

Date: 2026-06-28.

Status: controller pen-and-paper reproduction before Lean.  This is a
retained-passive chart-side measure-transport step.  It is independent of the
quiver-based paper and uses only Aoyagi's p.13 retained-passive chart layer
plus the previously formalised selected-entry signed-box calculation.

## Shape

Fix the retained-passive determinant-chart coordinate space

```text
Z = TopologyTuple rho kappa' R
S = topologyTupleDetChartSet.
```

For a determinant-chart coordinate `z`, let

```text
directChart(z) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W B U0 hU0 (ofTopologyTuple z)
```

and let

```text
Q(z) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap
      W B U0 hU0 (fun E => E) (directChart z)).
```

The existing inverse-Jacobian retained-passive handoffs still need the two
determinant-chart residual hypotheses

```text
for m.restrict S-a.e. z, 0 < Q(z),
integral^- ofReal (Q(z)^(-t)) dm.restrict S < infinity.
```

The selected-entry weighted-box theorem proves the corresponding facts on a
finite center signed box.  The handoff considered here assumes a concrete
selected-entry parametrisation of the determinant chart:

```text
chart : (center -> R) -> Z,

m.restrict S =
  map chart
    (signedBox.withDensity
      (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y))).
```

It also assumes the residual readout

```text
Q(chart y) = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

## Calculation

Let

```text
signedBox =
  Measure.pi (fun i : center => volume.restrict (Ioo (-(R i)) (R i))),

weightedBox =
  signedBox.withDensity
    (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y)).
```

The selected-entry theorem gives, under `0 <= t`, positive radii, and

```text
2 * t < ((center.erase pivot.1).card : R) + 1,
```

that

```text
for weightedBox-a.e. y,
  0 < SelectedEntrySignedBox.CenterCoord.residual pivot y,

integral^- ofReal
  ((SelectedEntrySignedBox.CenterCoord.residual pivot y)^(-t))
  dweightedBox < infinity.
```

Using the residual readout, this becomes

```text
for weightedBox-a.e. y, 0 < Q(chart y),

integral^- ofReal ((Q(chart y))^(-t)) dweightedBox < infinity.
```

For positivity on `m.restrict S`, use the supplied map equality.  If the target
positive set

```text
{z | 0 < Q(z)}
```

is measurable and `chart` is a.e. measurable on the signed box, then `chart`
is a.e. measurable on `weightedBox` by absolute continuity of `withDensity`.
Mathlib's `ae_map_iff` pushes the source a.e. statement through the map:

```text
for map chart weightedBox-a.e. z, 0 < Q(z).
```

Replacing `map chart weightedBox` by `m.restrict S` gives the determinant-chart
a.e. positivity conclusion.

For the finite lower integral, set

```text
f(z) = ofReal (Q(z)^(-t)).
```

The lower-integral map inequality gives

```text
integral^- f(z) d(map chart weightedBox)(z)
  <= integral^- f(chart y) dweightedBox(y).
```

The right-hand side is finite by the selected-entry theorem and the readout
`Q(chart y) = residual pivot y`.  Replacing `map chart weightedBox` by
`m.restrict S` gives the determinant-chart finite-integral conclusion.

## Lean target

Add in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

a theorem with content:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_map
```

It should consume:

- selected-entry center, pivot, radii, and exponent hypotheses;
- a.e. measurability of the determinant-chart map on the signed box;
- the determinant-chart pushforward equality above;
- measurability of `{z | 0 < Q(z)}`;
- the residual readout `Q(chart y) = residual pivot y`.

It should conclude exactly the two determinant-chart residual hypotheses used
by the raw-order retained-passive inverse-Jacobian handoffs.

## Boundary

This proves chart-side residual positivity and finite negative-power
integrability only under a supplied selected-entry determinant-chart
pushforward and residual readout.  It does not construct `chart`, prove chart
coverage, prove the determinant-chart measure comparison, identify an original
external DLN prior, prove local loss or density bounds, prove source-rank
coverage, construct normal crossings, compute a pole order, or extract an
RLCT.
