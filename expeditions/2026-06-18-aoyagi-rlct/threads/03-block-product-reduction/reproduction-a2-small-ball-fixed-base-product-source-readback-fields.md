# A2 small-ball fixed-base product source-readback fields reproduction

Date: 2026-06-30.

## Scope

This note packages the determinant-unit hypothesis in the fixed-base
product-coordinate source-readback theorem by a small Euclidean ball around
the origin in the p.13 regular variables.  It is independent of the quiver
paper.  It proves only local finite block algebra and continuity of the
regular `Ctop` determinant.  It does not prove source-prior transport, Haar
transport, source-image coverage, normal crossings, pole order, or RLCT
extraction.

## Setup

For a fixed-base p.13 regular-coordinate vector `u`, the decoded endpoint
block is

```text
Ctop(u) = I + B(u),
```

where the `B` part is one of the regular coordinate blocks.  At the regular
origin,

```text
Ctop(0) = I,
det(Ctop(0)) = 1.
```

The determinant map

```text
u ↦ det(Ctop(u))
```

is continuous.  Since being a unit in `R` is an open condition around `1`,
there is a radius `R > 0` such that

```text
u ∈ ball(0,R)  =>  IsUnit(det(Ctop(u))).
```

The existing Lean radius lemma gives this with an arbitrary upper bound
`R ≤ Rmax`.

## Consequence for readback

For any base edge-family point `x` and any `u` in this small ball, the generic
fixed-base product-coordinate source-readback theorem applies to
`CedgeProd(x,u)`.  Hence the field package is

```text
A1passive = 1,
F2        = first decoded F2 from u, then zeros,
A3passive = 0,
C         = residualBlock(fixedBase(CedgeBase x)),
Ctop      = decoded Ctop from u,
F3        = decoded F3 from u.
```

The radius depends only on the regular-coordinate type and `Rmax`, not on
`x`.  This is the local domain packaging needed for later chart-side use.

## Boundary

This is not a coverage theorem or a prior-transport theorem.  It only says
that after shrinking the regular Euclidean variables so `Ctop` stays
invertible, the fixed-base p.13 product chart has the same source-readback
fields as in the pointwise theorem.
