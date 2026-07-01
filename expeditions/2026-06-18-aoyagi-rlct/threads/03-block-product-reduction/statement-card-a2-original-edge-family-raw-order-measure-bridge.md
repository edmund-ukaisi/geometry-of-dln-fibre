# Statement Card - A2 Original Edge-Family Raw-Order Measure Bridge

## Claim

For the full-space continuous linear equivalence

```text
L := rawOrderMatrixTupleContinuousLinearEquiv e
```

from retained-passive raw-order tuple coordinates to original matrix tuple
coordinates, the pushforward of a restricted raw-coordinate Haar measure is a
full-space Haar scalar multiple of `originalTupleVolume` restricted to the
image:

```text
Measure.map L (m.restrict S)
= c • (originalTupleVolume d).restrict (L '' S)
```

where

```text
c := (Measure.map L m).addHaarScalarFactor (originalTupleVolume d).
```

Composing this with the existing retained-passive formal-product Jacobian COV
gives the same scalar-restricted original tuple measure for the image of the
raw-order source-recursive determinant chart.

## Public Lean Names

```text
map_rawOrderMatrixTuple_restrict_eq_smul_originalTupleVolume_restrict_image
map_formalProduct_rawOrderMatrixTuple_eq_smul_originalTupleVolume_restrict_image
```

## Inputs Used

- ambient raw-coordinate additive Haar measure `m`;
- the raw-order continuous linear equivalence
  `rawOrderMatrixTupleContinuousLinearEquiv e`;
- `originalTupleVolume d` and its Haar normalization;
- `MeasurableEquiv.restrict_map` for the image restriction;
- the existing formal-product retained-passive raw-order COV theorem
  `map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_rawSourceChart`;
- for the composed theorem, null-measurability of the determinant chart with
  respect to `m`.

## Output

For arbitrary raw set `S`:

```text
Measure.map L (m.restrict S)
= ((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
  (originalTupleVolume d).restrict (L '' S).
```

For the formal-product retained-passive raw-order chart:

```text
Measure.map (fun z => L (topologyTupleEdgeRawOrder z))
  ((m.restrict detChart).withDensity formalProductAbsDet)
= ((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
  (originalTupleVolume d).restrict (L '' rawSourceSet).
```

## Proof Shape

The first theorem is:

1. `Measure.map L (m.restrict S) = (Measure.map L m).restrict (L '' S)` by
   `MeasurableEquiv.restrict_map` and injectivity of `L`.
2. `Measure.map L m = c • originalTupleVolume d` by full-space Haar
   uniqueness.
3. Restrict the full-space equality and use `Measure.restrict_smul`.

The second theorem composes the existing formal-product COV theorem with the
raw-order tuple readout and then applies the first theorem with
`S := topologyTupleRawOrderSourceRecursiveDetChartSet`.

## Nonclaims

This is a scalar comparison after a full-space Haar uniqueness theorem and a
set restriction. It does not state that a restricted measure is Haar, does not
prove the scalar is `1`, and does not prove original edge-family volume
transport, source-image coverage, chart-piece domination, normal crossings,
pole order, or RLCT extraction.
