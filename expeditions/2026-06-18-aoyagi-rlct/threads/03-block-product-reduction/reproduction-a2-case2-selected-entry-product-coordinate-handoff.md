# A2 selected-entry product-coordinate handoff

## Source calculation

This note isolates the two-edge Case 2 selected-entry chart as a source for the
reduced p.13 product-coordinate map.  It is independent of the quiver paper.

Fix Aoyagi Case 2 data `n, S, J` with

```text
1 <= S,
J + 1 <= prefixMinNat n (S + 1),
J + 2 <= prefixMinNat n (S + 1).
```

Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1)
pivotNext = (J + 2, J + 2) in center.
```

For a target residual value `value : center -> R` with
`value pivotNext != 0`, the fixed-pivot selected-entry inverse is

```text
preimageOfPivotNeZero pivotNext value i
  = value pivotNext,       if i = pivotNext,
  = value i / value pivotNext, otherwise.
```

The selected-entry chart map sends this inverse back to `value`:

```text
chartMap pivotNext (preimageOfPivotNeZero pivotNext value) = value.
```

This is an elementary division calculation.  The nonzero-pivot hypothesis is
the only denominator condition.

## Fixed-base source chart

Let `sourceChart yNext` be the fixed-base p.13 source edge family attached to
the endpoint-transported retained-passive datum

```text
(case2PostPivotSelectedEntryRetainedPassiveData n hS hcont hnext yNext eNext)
  .endpointTransport e.
```

Use the value-coordinate source chart

```text
CedgeBase value = sourceChart (preimageOfPivotNeZero pivotNext value)
```

on the punctured source set

```text
source = { value : center -> R | value pivotNext != 0 }.
```

The existing selected-entry residual readout gives, for the residual-coordinate
equivalence `residualCoordEquiv`,

```text
paperEndpointFixedBaseResidualBlockCoordinateMap (CedgeBase value) c
  = value (residualCoordEquiv c).
```

Therefore the base readback

```text
baseReadback coord i = coord (residualCoordEquiv.symm i)
```

satisfies

```text
baseReadback
  (paperEndpointFixedBaseResidualBlockCoordinateMap (CedgeBase value))
    = value
```

for every `value in source`.

## Chart hypotheses

The direct selected-entry source chart `sourceChart` is already continuous as a
finite coordinate map.  The fixed-pivot inverse is continuous at every
`value` with `value pivotNext != 0`, because each coordinate is either
projection to the pivot coordinate or a quotient by that nonzero pivot
coordinate.  Hence `CedgeBase` is continuous at every point of `source`.

The endpoint-transported retained-passive datum lies in the determinant chart
for every `yNext`.  Equivalently, the source edge family `sourceChart yNext`
lies in the fixed-base retained-passive p.13 local source, so the recursive
identity-corner determinant hypotheses required by the p.13 product-coordinate
constructor hold for `CedgeBase value`.

## Lean target and boundary

The Lean target specializes the generic product-coordinate handoff to this
value-coordinate selected-entry source.  It proves the source measurability,
continuity, determinant-chart, and residual-readback inputs, then reuses the
generic product-coordinate source-side `withDensity` handoff.

It still assumes:

- the external weighted source-side pushforward identity through the product
  chart;
- a density a.e. measurability statement;
- a pointwise source-domain density bound.

It does not prove source/product measure transport for the original prior,
ambient raw-Haar transport, the normal-crossing-to-RLCT theorem, pole order, or
RLCT extraction.

Kill conditions:

- if `value pivotNext = 0`, the fixed-pivot inverse is not valid;
- if the source chart is taken on raw selected-entry coordinates `yNext`
  rather than value coordinates, the residual readback is `chartMap pivotNext
  yNext`, not `yNext`;
- if this is applied to full passive-theta coordinates, residual coordinates
  alone do not recover the passive variables.
