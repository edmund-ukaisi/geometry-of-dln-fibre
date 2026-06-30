# A2 generic fixed-base product source-readback fields reproduction

Date: 2026-06-30.

## Scope

This note records the generic fixed-base version of the p.13
product-coordinate source-readback calculation.  It is independent of the
quiver paper.  It proves only pointwise finite block algebra for the explicit
fixed-base product-coordinate chart.  It does not prove source-prior
transport, Haar transport, source-image coverage, normal crossings, pole
order, or RLCT extraction.

## Setup

Let `CedgeBase x` be an arbitrary base edge family in the fixed-base endpoint
chart for a chain with `M + 2` edges.  Let

```text
Ebase_p = fixedBase(CedgeBase x)_p.
```

The source-dependent p.13 product-coordinate constructor forms

```text
CedgeProd(x,u)
```

by decoding the regular Euclidean variables `u` into

```text
F2, F3, Ctop
```

and taking the residual factors

```text
C_p = residualBlock(Ebase)_p.
```

Write

```text
Eprod_p = fixedBase(CedgeProd(x,u))_p.
```

Assume `det(Ctop)` is a unit.

## Prescribed fixed-base matrices

By construction, `CedgeProd(x,u)` is the continuous edge-family realisation of
the prescribed matrix family

```text
G_p = productCoordinateMatrix(u, Ebase)_p.
```

The fixed-base realisation theorem gives

```text
Eprod = G.
```

Unfolding the product-coordinate matrix family gives the raw p.13 shapes:

```text
G_last = [ I      0        ; -F3  C_last ],
G_p    = [ I      0        ; 0    C_p    ]    for 0 < p < last,
G_0    = [ Ctop   -Ctop F2 ; 0    C_0    ].
```

Thus the fixed-base product chart satisfies exactly the hypotheses of the raw
multi-edge product-coordinate source-readback theorem.

## Source-readback fields

Applying the raw theorem gives

```text
sourceReadback(Eprod).A1passive = 1,
sourceReadback(Eprod).F2 = first F2, then zeros,
sourceReadback(Eprod).A3passive = 0,
sourceReadback(Eprod).C = C,
sourceReadback(Eprod).Ctop = Ctop,
sourceReadback(Eprod).F3 = F3.
```

Here `C` is the residual-block family extracted from `Ebase`, not a new
coverage or inverse assertion.

## Boundary

The theorem says what the explicit product-coordinate chart reads back to in
fixed-base coordinates.  It is not a full inverse theorem for an original
parameter, and it is not a measure or prior-transport theorem.  In particular,
the retained passive fields are canonicalized to `A1passive = 1` and
`A3passive = 0`; they are not recovered from an arbitrary passive-theta point.
