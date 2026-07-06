# A2 p.13 Original Density Composed Finite Integral

## Source Calculation

Aoyagi's local zeta function uses a prior density `phi(w)`.  In the DLN
specialization the prior is assumed smooth, compactly supported, and positive
at the true parameter.  The p.13 product-coordinate calculation rewrites the
local variables as retained source variables together with the regular
variables `(Ctop - I, F2, F3)`.

In Lean the explicit self-base p.13 product-coordinate edge-family map is:

```text
CedgeProd : alpha x EuclideanSpace R Coord -> EdgeFamily.
```

For an original edge-family density

```text
phi : EdgeFamily -> R,
```

the product-coordinate density in the local zeta integrand is:

```text
Phi(x,u) = phi(CedgeProd(x,u)).
```

The previous continuity bridge proves:

```text
ContinuousAt phi (CedgeProd(x0,0))
0 < phi(CedgeProd(x0,0))
```

imply

```text
ContinuousAt Phi (x0,0)
0 < Phi(x0,0).
```

The existing signed-box finite-integral front end takes as hypotheses:

```text
ContinuousAt density (x0,0)
0 < density (x0,0),
```

together with the already explicit residual signed-box source hypotheses,
source-density monomial bounds, local product-family construction, fixed-basis
edge-matrix measurability, and the original-loss comparison already handled by
the parent original-loss wrapper.  Substituting

```text
density = Phi
```

and applying the continuity bridge gives the same finite integral with
integrand

```text
lossDLN(...) ^ (-(t + regularVariableCount / 2)) * phi(CedgeProd(x,u)).
```

This is a finite-integral consumer of the p.13 product-coordinate density
bridge.  It does not alter the source measure, and it does not assert that the
original prior measure is the pushforward or pullback of the product-coordinate
measure.

## Boundary

The residual signed-box chart, weighted pushforward, source-density
nonnegativity and monomial upper bound, residual monomial lower bound, local
product-family construction, fixed-base edge-matrix measurability, and
the parent original-loss comparison wrapper remain part of the route.

This proves no change-of-variables formula for the original prior, no
original-prior measure transport, no chart-piece a.e. domination by original
edge-family volume, no source-image identity, no source coverage, no
determinant/raw Haar transport, no normal crossings, no pole order, and no
RLCT extraction.

## Kill Conditions

- Kill any use that reads the finite integral as an original-prior measure
  transport theorem.
- Kill any use that drops the signed-box source-density and residual-monomial
  hypotheses.
- Kill any use that treats this as a global prior-density statement; the
  density input is only continuity and positivity at the base product-coordinate
  image.
