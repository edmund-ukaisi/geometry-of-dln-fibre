# A2 product residual finite integral from right-invertible following factors

Date: 2026-07-02.

## Source calculation

In the enlarged Case 2 passive-theta source, write

```text
D(y) = active C 1 residual block,
F    = following C 0 factor,
P(y,F) = D(y) F.
```

The earlier active-readout theorem proves positivity and finite negative-power
integrability for

```text
A(y) = square_sum(D(y))
```

over the product source measure with finite passive mass and finite following
mass.  The p.13 residual product, however, is

```text
B(y,F) = square_sum(P(y,F)).
```

Finite following mass alone is not enough to compare `A` and `B`: if `F` has a
kernel or is zero, then `D F` can vanish even when `D` is nonzero.  The needed
local socket is nondegeneracy of `F`.

Assume a.e. on the local following-factor patch that every `F` has a right
inverse `G` with a uniform coordinate square-sum bound

```text
F G = I,
square_sum(G) <= K.
```

Then

```text
D = D (F G) = (D F) G.
```

The finite Frobenius coordinate estimate gives

```text
square_sum(D) <= square_sum(D F) square_sum(G) <= K' square_sum(D F),
```

where `K' = max(1,K)`.  Hence for `c = 1 / K' > 0`,

```text
c square_sum(D) <= square_sum(D F).
```

This lower bound is the correct direction for negative powers.  If `t >= 0`
and `A > 0`, then

```text
B >= c A > 0,
B^(-t) <= (c A)^(-t) = c^(-t) A^(-t).
```

Thus the finite integral of `A^(-t)` transfers to the finite integral of
`B^(-t)`.

## Lean artifacts

The finite reindexing bridge between the active displayed residual block and
the selected-entry active readout is:

```text
Case2PassiveThetaWithFollowingFactor.displayedPostPivotResidualBlock_squareSum_eq_activeReadout_squareSum
```

The measure-level comparison consumer is:

```text
case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_ae_const_mul_activeReadout_le
```

The p.13-facing right-inverse wrapper is:

```text
case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_ae_followingFactor_rightInverse_squareSum_le
```

## Boundary

This proves a conditional local finite-integral bridge for the true two-edge
p.13 product residual under an a.e. uniformly bounded right-inverse hypothesis
for the following factor.  It does not construct the following-factor patch,
prove openness of full-row-rank factors, identify a concrete endpoint
neighborhood where the hypothesis holds, transport source or original priors,
prove normal crossings, compute pole order, or extract the RLCT.
