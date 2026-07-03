# A2 p.13 Product-Coordinate Prior-Density Continuity

## Source calculation

Aoyagi assumes the prior density is smooth and positive at the base parameter:
Definition 1 introduces the prior density, and the DLN setup on p.8 assumes
the prior is smooth, compactly supported, and positive at the chosen point.

The p.13 product coordinates add the regular variables `(Ctop - I, F2, F3)` to
the retained passive source variables.  In Lean the explicit p.13 product map
is:

```text
CedgeProd :
  alpha x EuclideanSpace R (AoyagiRegularBlockCoordinateIndex ...) -> EdgeFamily.
```

The already-landed coordinate algebra proves `CedgeProd` is continuous at the
base product point `(x0,u0)` in the self-base situation.  Therefore, for any
original prior density `phi : EdgeFamily -> R`,

```text
ContinuousAt phi (CedgeProd (x0,u0))
```

implies

```text
ContinuousAt (fun z => phi (CedgeProd z)) (x0,u0).
```

If also

```text
0 < phi (CedgeProd (x0,u0)),
```

then the pulled-back product-coordinate density is positive at `(x0,u0)`.

## Boundary

This is only the local continuity/positivity input for downstream finite
integral theorems.  It does not prove a change-of-variables identity, an
original-prior pushforward or pullback measure formula, local boundedness on a
specific measurable chart piece, source-image equality, source coverage,
normal crossings, pole order, or RLCT.
