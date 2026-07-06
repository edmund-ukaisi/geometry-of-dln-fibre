# A2 p.13 Product-coordinate Readback Left Inverse

## Source Calculation

Aoyagi p.13 separates the local variables into a residual source part and
regular variables.  In Lean, the reduced fixed-base product-coordinate map is:

```text
CedgeProd(x,u) =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    V Bv U0 hU0 CedgeBase (x,u).
```

The regular variable `u` decodes the blocks

```text
Ctop(u), F2(u), F3(u),
```

and the base point `x` supplies residual blocks

```text
C_p(x) = residualBlock(Ebase(x), last, p).
```

The constructed matrix family has endpoint/middle block form:

```text
p = 0:       [ Ctop(u), -Ctop(u) F2(u); 0, C_0(x) ]
0 < p < N:  [ I,        0;              0, C_p(x) ]
p = last:   [ I,        0;             -F3(u), C_last(x) ].
```

For sufficiently small `u`, `det Ctop(u)` is a unit.  The already-proved
coordinate recovery theorem then gives:

```text
regularBlockCoordinateMap(CedgeProd(x,u)) = u,
residualBlockCoordinateMap(CedgeProd(x,u))
  = residualBlockCoordinateMap(CedgeBase x).
```

Therefore any residual readback

```text
baseReadback(residualBlockCoordinateMap(CedgeBase x)) = x
```

extends to a product readback on edge families:

```text
productReadback(E) =
  ( baseReadback(residualBlockCoordinateMap(E)),
    regularBlockCoordinateMap(E) ).
```

Applying this to `CedgeProd(x,u)` recovers `(x,u)`.  Consequently
`CedgeProd` is injective on any product region where the residual readback is a
left inverse on the base source set and `det Ctop(u)` stays a unit.  The small
ball determinant theorem supplies such a region around `u = 0`.

## Lean Targets

The landed pointwise theorem is:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_productReadback_leftInverse_of_residualReadback
```

The landed set-level consequences are:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_injOn_of_residualReadback

exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_injOn_of_residualReadback
```

All are in:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean
```

## Boundary

This is a pointwise and set-level readback/injectivity layer only.  It does
not prove continuity on the product domain, image measurability, source-image
coverage, a product-coordinate measure pushforward, original-prior transport,
normal crossings, pole order, or RLCT extraction.

It also does not turn the reduced p.13 raw section into a full raw-Haar chart.
The reduced section fixes transverse raw variables such as `C1 = I` and
`A3 = 0`, so its pushforward cannot be full Haar measure on the raw determinant
chart.

## Checks

Xhigh explorer `Euclid` found no existing full inverse API for `CedgeProd`,
but identified exactly this residual-readback left-inverse theorem as the next
missing layer.  Xhigh source scout `Arendt` independently reconstructed the
p.13 reduced-section formulas and confirmed the raw-Haar boundary.

## Kill Conditions

- Kill any use as a measure transport theorem.
- Kill any use as source-image coverage or image equality.
- Kill any use as full raw-Haar pushforward from the reduced p.13 raw section.
- Kill any use that assumes a residual readback without supplying the
  left-inverse hypothesis on the base source set.
