# Reproduction - A2 suffix-state step coordinate adapter

Status: pen-and-paper reproduction before Lean wrapper formalisation.

## Source Anchor

The previous p. 13 wrapper proved that a raw coordinate package gives the
next triangular product and product-difference block, assuming a prior product
hypothesis

```text
[I 0; F3old I] T = [C1 0; 0 D] [A1 A2; A3 A4].
```

This slice instantiates that hypothesis from the deterministic suffix-state
invariant.  It is still finite block algebra: no openness, analytic chart,
ideal transport, normal crossings, pole order, or RLCT is involved.

## Suffix-State Data

Let

```text
S : ChartLocalSuffixState rho kappa K j p.succ
hS : S.BlockDiagonal P hpj
M  = transformedEdge E p S
Rprev = [I  -S.B; 0 I].
```

By definition,

```text
M = [I S.B; 0 I] E_p,
```

so

```text
E_p = Rprev M
```

because `[I -S.B; 0 I] [I S.B; 0 I] = I`.

The suffix product recursion supplies

```text
P p.castSucc j = P p.succ j * E_p.
```

The block-diagonal invariant says

```text
S.L * P p.succ j * Rprev = [S.Ctop 0; 0 S.D].
```

If the accumulated left multiplier is lower unitriangular,

```text
S.L = [I 0; F3old I],
```

then

```text
[I 0; F3old I] * P p.castSucc j
  = [S.Ctop 0; 0 S.D] * M.
```

This is exactly the prior product hypothesis for the one-step p. 13
coordinate theorem, with

```text
T = P p.castSucc j.
```

The matrix `T` is not `M`; `M` is the transformed one-edge block whose corners
provide the raw variables.

## Raw Coordinates

Build the raw coordinate package from `S`, `F3old`, and the corners of `M`:

```text
C1 = S.Ctop,
D  = S.D,
F3 = F3old,
A1 = topLeftCorner M,
A2 = upperRightBlock M,
A3 = lowerLeftBlock M,
A4 = lowerRightBlock M.
```

The determinant-chart hypotheses are:

```text
IsUnit S.Ctop.det,
identityCornerDetChart M.
```

The first is contained in `S.BlockDiagonal`; the second is the recursive
determinant-chart assumption for the transformed edge.  No determinant or
inverse hypothesis on `S.D` is used.

## Chart Fields

For `x` the raw coordinate package and `y = x.toChart`,

```text
y.Ctop = (step E p S).Ctop,
y.F2   = -(step E p S).B,
y.C    = schurResidualBlock M,
y.D*y.C = (step E p S).D.
```

If `S.L = [I 0; F3old I]`, then

```text
y.F3 = lowerLeftBlock (step E p S).L.
```

The last equality uses multiplication of lower unitriangular matrices:

```text
[I 0; -S.D A3 (S.Ctop A1)^(-1) I] [I 0; F3old I]
  = [I 0; F3old - S.D A3 (S.Ctop A1)^(-1) I].
```

## Product-Difference Consequence

Applying the previous p. 13 wrapper to these raw coordinates gives

```text
[I 0; y.F3 I] (P p.castSucc j) [I y.F2; 0 I]
  = [y.Ctop 0; 0 y.D y.C],
```

and after subtracting `[I 0; 0 0]`,

```text
[I 0; y.F3 I] (P p.castSucc j - [I 0; 0 0]) [I y.F2; 0 I]
  = [y.Ctop - I, -y.F2; -y.F3, y.D y.C - y.F3 y.F2].
```

In step fields, this is the same signed/corrected p. 13 block with
`F2 = -(step.B)`, `F3 = lowerLeftBlock step.L`, and residual block `step.D`.

## Lean Plan

Implement the adapter in `ProductReduction.lean`, inside
`ChartLocalSuffixState` and before the recursive suffix-state definitions:

```text
stepRawCoordinates
stepRawCoordinates_detChart
stepRawCoordinates_toChart_Ctop
stepRawCoordinates_toChart_F2
stepRawCoordinates_toChart_C
stepRawCoordinates_toChart_D_mul_C
stepRawCoordinates_toChart_F3_of_L_eq_lowerUnitriangular
stepRawCoordinates_priorProduct
stepRawCoordinates_triangularBlockProduct
stepRawCoordinates_productDifference
```

## Nonclaims

This slice does not prove lower-unitriangularity from `BlockDiagonal`; it takes
the witness `S.L = [I 0; F3old I]`.  For actual suffix states this witness is
provided separately by `suffixState_L_eq_lowerUnitriangular`.  This slice also
does not prove exact-rank openness, chart coverage, analytic germ transport,
ideal transport, normal crossings, pole order, or RLCT.
