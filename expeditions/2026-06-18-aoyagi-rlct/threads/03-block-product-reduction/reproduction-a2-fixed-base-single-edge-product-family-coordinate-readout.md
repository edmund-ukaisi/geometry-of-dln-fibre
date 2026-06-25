# Reproduction - A2 fixed-base single-edge product-family coordinate readout

Date: 2026-06-25.

Status: pen-and-paper reproduction for the fixed-base p.13 readout in the
single-edge product-family case.

## Calculation

For a one-edge chain the right and left endpoint product-family steps collapse
into one transformed edge.  The already-checked matrix theorem uses the block
shape

```text
[ Ctop,        -Ctop F2
  -F3 Ctop,    C0 + F3 Ctop F2 ].
```

The Schur residual of this block is

```text
(C0 + F3 Ctop F2) - (-F3 Ctop) Ctop^{-1} (-Ctop F2)
  = C0.
```

The suffix-state fields are therefore

```text
S.B    = -F2,
S.Ctop = Ctop,
S.D    = C0,
S.L    = [I, 0; F3, I].
```

The fixed-base p.13 coordinate map reads those fields as

```text
value(S.Ctop - I, -S.B, lowerLeftBlock S.L, S.D)
  = value(Ctop - I, F2, F3, C0).
```

The prescribed-matrix version is the same calculation after realizing the
fixed-base edge matrix by `Matrix.toLin` and `LinearMap.toContinuousLinearMap`.

## Lean Target

```text
paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdge_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdge_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrix_one
```

## Boundary

This is only the single-edge endpoint-collapse case.  It does not construct a
product-coordinate matrix family, prove transformed-edge shapes for such a
family, prove parameter-continuity, source coverage, signed-box pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction.
