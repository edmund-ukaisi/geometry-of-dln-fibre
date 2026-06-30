# A2 generic fixed-base small-ball product readout package

This note records the generic fixed-base p.13 small-ball package behind the
concrete Case 2 product-readout theorem.  It is independent of the quiver
paper and uses only Aoyagi's p.13 product-coordinate algebra plus elementary
determinant continuity.

## Setup

Let `CedgeBase x` be an arbitrary fixed-base edge family over a parameter
type `alpha`.  The p.13 source-dependent product-coordinate constructor forms

```text
CedgeProd(x,u)
```

by decoding the regular Euclidean variable `u` into

```text
F2(u), Ctop(u), F3(u)
```

and by taking residual factors from the fixed-base matrix family associated to
`CedgeBase x`:

```text
C(p) = residualBlock(fixedBase(CedgeBase x), last, p).
```

At `u = 0`, the decoded top block is `Ctop(0) = I`.  Since determinant is
continuous, for every `Rmax > 0` there is `0 < R <= Rmax` such that every
`u in ball(0,R)` has `IsUnit det(Ctop(u))`.

## Shared-radius consequences

Fix `x` and `u in ball(0,R)`.  The determinant-unit certificate is then
available for every pointwise p.13 readout theorem.

The raw coordinate-map readout gives

```text
regularCoordinateMap(CedgeProd(x,u)) = u
residualCoordinateMap(CedgeProd(x,u))
  =
residualCoordinateMap(CedgeBase x).
```

The generic source-readback field formula gives, for

```text
Ebase = fixedBase(CedgeBase x),
Eprod = fixedBase(CedgeProd(x,u)),
data  = sourceReadback(Eprod),
```

the six field equalities

```text
data.A1passive = 1
data.F2        = first decoded F2(u), then zeros
data.A3passive = 0
data.C         = C
data.Ctop      = Ctop(u)
data.F3        = F3(u).
```

The package records these facts under one radius rather than forcing later
callers to invoke the determinant-neighborhood theorem separately for each
readout.

## Boundary

This is local fixed-base coordinate algebra.  It does not recover an original
parameter, prove source-image coverage, identify a source prior, prove
Haar/Jacobian transport, establish normal crossings, compute pole order, or
extract an RLCT.  The retained passive fields are canonicalized by
`sourceReadback`; they are not recovered from a general passive source point.
