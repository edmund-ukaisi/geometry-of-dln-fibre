# Reproduction - A2 retained-passive DetData continuity to a.e. measurability

## Claim

The retained-passive source-edge-family finite-integral handoffs ask for

```text
AEMeasurable (fun y => <retainedData y, hdet y> : DetData) signedBox.
```

For constructed Aoyagi chart data, the natural input is usually stronger:

```text
Continuous (fun y => <retainedData y, hdet y> : DetData).
```

The helper proves that continuity supplies the a.e. measurability hypothesis
for the selected-entry signed-box measure.

## Calculation

Let

```text
DetData := {data : RetainedPassiveNonredundantCoordinateData // data.detChart}
signedBox := product_i volume.restrict (-Rres_i, Rres_i).
```

If `DetData` is a Borel measurable space and the coordinate map

```text
y |-> <retainedData y, hdet y>
```

is continuous, then Mathlib's Borel-space theorem gives measurability of this
map.  Measurability immediately implies a.e. measurability with respect to
any measure, in particular `signedBox`.

## Boundary

This is only a measurability adapter.  It does not construct the retained data,
prove determinant-chart membership, prove source-image or residual identities,
perform any Jacobian comparison, or prove any finite integral by itself.
