# Reproduction - A2 following-factor right-inverse product comparison

Date: 2026-07-02.

Status: controller pen-and-paper reproduction for the next p.13-facing
comparison brick.

## Source Boundary

In the enlarged Case 2 with-following source, the active selected-entry block
is a matrix `D(y)` and the independent following factor is a matrix `F`.  The
p.13 residual coordinate map reads the full two-edge product

```text
D(y) * F
```

not `D(y)` alone.  The active-readout theorem already proves finite
negative-power integrability for the coordinate square-sum of `D(y)`.  To
transfer that theorem to the true p.13 residual product, we need a local
nondegeneracy/comparison hypothesis on `F`.

The elementary finite-dimensional hypothesis that suffices is: `F` has a right
inverse `G`, with `F * G = 1`, and the coordinate square-sum of `G` is bounded
by a uniform constant `K`.

## Calculation

Let

```text
D : Matrix mu iota R
F : Matrix iota nu R
G : Matrix nu iota R
```

over `R = real`, with `F * G = 1`.  Then

```text
(D * F) * G = D * (F * G) = D.
```

The existing finite coordinate estimate in Lean is

```text
matrixCoordinateSquareSum_mul_le_mul
```

which states

```text
sq(A * B) <= sq(A) * sq(B)
```

for the coordinate square-sum `sq(M) = sum_{ij} M_ij^2`.  Apply it to
`A = D * F` and `B = G`:

```text
sq(D) = sq((D * F) * G) <= sq(D * F) * sq(G).
```

If `sq(G) <= K` and `0 <= c`, `c*K <= 1`, then

```text
c * sq(D)
  <= c * (sq(D * F) * sq(G))
  <= c * (sq(D * F) * K)
  = (c*K) * sq(D * F)
  <= sq(D * F).
```

Taking `K = max 1 sq(G)` and `c = K^-1` gives a positive constant for a fixed
right inverse.  More useful downstream is the uniform version: on a following
factor patch where every `F` has some right inverse `G(F)` with `sq(G(F)) <= K`,
the single constant `c = (max 1 K)^-1` works for every `F` in the patch.

## Negative-Power Transfer

Let

```text
a(z) = sq(D(y))
b(z) = sq(D(y) * F)
```

and assume `0 < c` and `c * a(z) <= b(z)` almost everywhere.  If `a(z) > 0`
almost everywhere and

```text
integral of ofReal(a(z)^(-t)) is finite
```

with `0 <= t`, then the existing Lean theorem

```text
lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le
```

transfers finite integrability to `b(z)`.  This is the exact inequality
direction needed: the product residual must be bounded below by a positive
constant times the active residual square-sum.

## Kill Conditions

- Finite following-factor mass alone is insufficient.  If `F = 0`, the product
  residual is zero and a.e. positivity fails.
- A left inverse `G * F = 1` is the wrong shape for right multiplication
  unless paired with additional hypotheses; the calculation needs
  `(D * F) * G = D`.
- The uniform source theorem needs a uniform bound on `sq(G)`, not merely
  pointwise existence of right inverses with unbounded inverse size.
- If the following matrix has too few columns to admit a right inverse, the
  hypothesis is false.  In the current Case 2 endpoint setup, endpoint
  equivalences supply the matching coordinate types; actual right-invertibility
  of an arbitrary following factor remains a separate local-patch hypothesis.

## Lean Target

The first bedrock theorem should live with the coordinate square-sum estimates
in `RegularSuspensionCoordinates.lean`:

```text
const_mul_matrixCoordinateSquareSum_le_mul_right_of_rightInverse_squareSum_le
```

and an existential fixed-`F` wrapper:

```text
exists_pos_const_forall_matrixCoordinateSquareSum_le_mul_right_of_mul_eq_one
```

The p.13-facing with-following theorem can then assume an a.e. comparison of
this form, or derive it from a local following-factor patch with a uniformly
bounded right inverse.

## Nonclaims

This note does not construct the local following-factor patch, prove openness
of the right-invertible locus, transfer negative-power integrability, prove
determinant-Haar transport, source-prior transport, normal crossings, pole
order, or RLCT extraction.
