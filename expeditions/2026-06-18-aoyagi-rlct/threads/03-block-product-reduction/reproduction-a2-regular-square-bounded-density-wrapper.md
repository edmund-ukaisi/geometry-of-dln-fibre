# Reproduction - A2 regular-square bounded-density wrapper

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for a finite-side
regular-square-suspension comparison theorem.

## Source Motivation

Aoyagi p. 13 separates the regular blocks `C1-Er`, `F2`, `F3` from the
residual product block `prod_s C^(s)` after the Theorem 3 product reduction.
The regular-variable shift in the paper needs more than finite block algebra:
one must still supply a product chart, a lower comparison of the actual loss
with the regular-plus-residual square model, and a transported density/prior
bound.

This slice proves only the measure-theoretic finite-side consequence once
those hypotheses are supplied.

The `ball(0,R)` in this note is only the regular-fiber ball in the `E`
variable.  Any base-domain, chart-neighborhood, or source-stratum restriction
must already be encoded in the base measure `mu`.

## Derivation

Let `E` be the regular-variable Euclidean/Haar factor and write

```text
a(x) = squareSum(b(x)).
```

Let

```text
s = t + dim(E)/2.
```

The existing residual-power threshold-shift theorem says that if

```text
a(x) > 0  a.e.
int^- x, ofReal(a(x)^(-t)) < infinity
```

with `t>0`, then

```text
int^- (x,u), ofReal((ball(0,R).indicator
  (fun u => (a(x)+||u||^2)^(-s)) u)) < infinity.
```

Now assume the supplied chart-side bounds on the regular ball:

```text
c * (a(x)+||u||^2) <= loss(x,u),     c > 0,
0 <= density(x,u),
density(x,u) <= C,                  C >= 0.
```

Again, the regular ball restricts only the `u : E` variable; it does not
construct or shrink the base chart domain.

At any point in the regular ball, `a(x)>0`, hence

```text
q = a(x)+||u||^2 > 0.
```

Since `s >= 0`, the exponent `-s` is nonpositive, so the lower loss bound
reverses under real powers:

```text
loss(x,u)^(-s) <= (c*q)^(-s)
                = c^(-s) * q^(-s).
```

Multiplying by the nonnegative density and then using the upper density bound
gives

```text
loss(x,u)^(-s) * density(x,u)
  <= c^(-s) * C * (a(x)+||u||^2)^(-s).
```

Outside the regular ball, both supported integrands are zero.  Therefore the
actual loss-density lower integral is bounded by the constant
`c^(-s)*C` times the already finite square-suspension model integral.

## Lean Shape

Lean proves this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

with names

```text
lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

The first theorem is stated for a general finite coordinate family
`b : alpha -> eta -> R`.  The second specialises `b` to residual matrix-block
entries `AoyagiResidualBlockCoordinateIndex.value (D x)`.

## Boundary

This theorem is a one-sided finite-integrability wrapper.  It does not prove:

- Aoyagi's p. 13 analytic product chart;
- the actual lower loss bound;
- Jacobian/prior density transport or boundedness;
- residual positivity or residual negative-power integrability;
- threshold equality, endpoint behavior, or divergence;
- pole-order preservation;
- normal crossings or RLCT extraction.
