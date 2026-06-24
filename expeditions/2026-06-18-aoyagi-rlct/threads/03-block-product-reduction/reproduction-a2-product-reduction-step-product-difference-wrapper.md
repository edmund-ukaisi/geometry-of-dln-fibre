# Reproduction - A2 product-reduction step product-difference wrapper

Status: pen-and-paper reproduction before Lean wrapper formalisation.

## Source Anchor

Aoyagi p. 13 passes from one determinant-chart product-reduction step to the
displayed product-difference block

```text
C1 - Er,   -F2,   -F3,   prod_s C^(s) - F3 F2.
```

The previous slice packaged the triangular coordinate formulas.  This slice is
the next elementary block-algebra wrapper: if a previous accumulated triangular
multiplier has already identified a matrix `T` with the raw two-block product,
then the new coordinates give the next diagonal product and, after subtracting
the rank-model block, the displayed signed/corrected product-difference block.

## Raw And Chart Variables

Use the raw one-step variables

```text
C1 : rho x rho,
D  : pi x mu,
F3old : pi x rho,
A1 : rho x rho,
A2 : rho x nu,
A3 : mu x rho,
A4 : mu x nu.
```

On the determinant chart, define

```text
Ctop = C1 A1,
F2   = - A1^(-1) A2,
F3   = F3old - D A3 (C1 A1)^(-1),
C    = A4 - A3 A1^(-1) A2.
```

Only `C1`, `A1`, and `C1 A1` are inverted in the calculation.  The residual
block `D` is not inverted.

## Prior Product Hypothesis

Assume the previous accumulated lower triangular multiplier has already
produced

```text
[I 0; F3old I] T =
  [C1 0; 0 D] [A1 A2; A3 A4].
```

This is the one-step source-facing form of the suffix-state invariant.  It
does not identify `D` with a raw product of original lower-right blocks; in the
recursive suffix formalisation `D` is the transformed residual product.

## Diagonal Product Check

Let

```text
X = D A3 (C1 A1)^(-1).
```

Then

```text
[I 0; F3 I] = [I 0; -X I] [I 0; F3old I],
```

because lower unitriangular blocks multiply by adding the lower-left blocks and
`F3 = F3old - X`.

Therefore

```text
[I 0; F3 I] T [I F2; 0 I]
  = [I 0; -X I] [C1 0; 0 D] [A1 A2; A3 A4] [I -A1^(-1)A2; 0 I].
```

The already-proved Schur block-elimination calculation gives

```text
[I 0; -X I] ([C1 0; 0 D] [A1 A2; A3 A4])
  [I -A1^(-1)A2; 0 I]
= [C1 A1 0; 0 D (A4 - A3 A1^(-1) A2)].
```

In chart variables this is

```text
[I 0; F3 I] T [I F2; 0 I] = [Ctop 0; 0 D C].
```

## Product-Difference Check

Let the rank-model block be

```text
T0 = [I 0; 0 0].
```

Using the diagonal product identity,

```text
[I 0; F3 I] (T - T0) [I F2; 0 I]
  = [Ctop 0; 0 D C] - [I, F2; F3, F3 F2]
  = [Ctop - I, -F2; -F3, D C - F3 F2].
```

The lower-right correction is `F3 F2`, not `F2 F3`: `F3` has shape
`pi x rho`, `F2` has shape `rho x nu`, and `F3 F2` has the same shape
`pi x nu` as `D C`.

## Lean Plan

Implement two algebraic wrapper theorems in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`:

```text
productReductionStepCoordinate_triangularBlockProduct
productReductionStepCoordinate_productDifference
```

The first theorem consumes the prior product hypothesis and uses the already
proved one-step block-elimination identity.  The second theorem applies the
already proved `triangularBlockProductDifference_fromBlocks_indexed`.

## Nonclaims

This is finite block algebra only.  It does not prove exact-rank or source-rank
openness, analytic coordinate-chart status, chart coverage, analytic germ
transport, Jacobian/prior compatibility, regular-suspension construction,
normal crossings, pole order, or RLCT extraction.
