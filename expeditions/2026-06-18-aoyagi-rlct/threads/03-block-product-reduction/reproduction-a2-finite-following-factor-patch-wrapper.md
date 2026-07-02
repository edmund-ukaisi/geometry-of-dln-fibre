# A2 finite following-factor patch wrapper

Date: 2026-07-02.

## Pen-and-paper reproduction

The previous theorem proves p.13 product-residual finite integrability from an
a.e. source-side right-inverse socket:

```text
for a.e. (theta,F), exists G with F G = I and square_sum(G) <= K.
```

For a local following-factor patch `s`, this socket follows from two elementary
inputs:

```text
followingMeasure(s) < infinity,
for every F in s, exists G with F G = I and square_sum(G) <= K.
```

Use the restricted following measure `followingMeasure.restrict s`.  If `s` is
measurable, then

```text
F in s for a.e. F with respect to followingMeasure.restrict s.
```

Taking the product with the passive-theta source measure and projecting to the
second factor gives

```text
F in s for a.e. (theta,F)
```

with respect to

```text
(passiveMeasure.prod weightedBox).prod (followingMeasure.restrict s).
```

The pointwise patch hypothesis then supplies the same right-inverse witness and
the same uniform square-sum bound `K` almost everywhere.  The previously proved
right-inverse product-residual theorem applies unchanged, with finite following
mass supplied by `followingMeasure(s) < infinity`.

## Lean target

The target theorem should be a thin wrapper:

```text
case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_rightInverse_squareSum_le
```

It consumes:

```text
MeasurableSet followingPatch
followingMeasure followingPatch < infinity
forall F in followingPatch, exists G, F * G = 1 and square_sum(G) <= K
```

and concludes positivity and finite negative-power integrability for the true
p.13 product residual over the source measure with following factor restricted
to `followingPatch`.

## Boundary

This packages a finite local patch; it does not construct an open patch, prove
that full-row-rank/right-invertible following factors form a neighborhood of a
chosen base point, or prove a singular-value lower bound from topology.  It
also does not perform source-prior/original-prior transport, prove normal
crossings, compute pole order, or extract RLCT.
