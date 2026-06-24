# Reproduction - A2 product-reduction triangular coordinate chart

Status: pen-and-paper reproduction before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 performs the determinant-chart block reduction step and then
uses variables whose displayed product-difference block is

```text
C1 - Er,   -F2,   -F3,   prod_s C^(s) - F3 F2.
```

The source-facing point of this slice is narrower than regular-suspension
additivity: reproduce the elementary triangular change of variables behind
those displayed variables.  It should explain why the scalar blocks
`C1-Er`, `F2`, and `F3` are plausible local coordinates before any attempt to
build a full normal-crossing certificate.

## One-Step Variables

Work on one determinant chart.  Use block variables

```text
C1' : r x r,
D_S : p x m,
F3' : p x r,
A1' : r x r,
A2' : r x n,
A3' : m x r,
A4' : m x n.
```

Aoyagi's literal source wording has `C1'` regular from the induction and then
takes the chart where `C1' A1'` is regular, while the p. 13 formulas also use
`(A1')^(-1)`.  In the Lean coordinate package we use the equivalent
determinant-domain presentation with `C1'` and `A1'` determinant units; then
`C1' A1'` is determinant-unit automatically.  The passive variables are

```text
D_S, A1', A3'.
```

They must be retained in the coordinate chart; dropping them would lose
dimension balance and would make the inverse impossible to state.

## Forward Coordinates

Define target coordinates

```text
C1''       = C1' A1',
F2''       = -(A1')^(-1) A2',
F3''       = F3' - D_S A3' (C1' A1')^(-1),
C^(S+1)    = A4' - A3' (A1')^(-1) A2',
```

together with the passive coordinates `D_S`, `A1'`, and `A3'`.

These formulas use inverses of `C1' A1'` and `A1'`, but not an inverse of
`D_S`.

## Inverse Coordinates

Given target data

```text
C1'', F2'', F3'', C^(S+1), D_S, A1', A3',
```

with `A1'` and `C1''` determinant-unit, recover the raw variables by

```text
C1' = C1'' (A1')^(-1),
A2' = - A1' F2'',
A4' = C^(S+1) - A3' F2'',
F3' = F3'' + D_S A3' (C1'')^(-1),
```

and keep `D_S`, `A1'`, and `A3'` fixed.

The formula for `A4'` is the same as
`C^(S+1) + A3' (A1')^(-1) A2'`, because
`(A1')^(-1) A2' = -F2''`.  Again, no inverse of `D_S` appears.

## Forward-Then-Inverse Check

Starting from raw variables, the inverse recovers:

- `C1'` because `(C1' A1') (A1')^(-1) = C1'`;
- `A2'` because `-A1' (-(A1')^(-1) A2') = A2'`;
- `A4'` because
  `(A4' - A3'(A1')^(-1)A2') - A3' (-(A1')^(-1)A2') = A4'`;
- `F3'` because
  `F3' - D_S A3'(C1'A1')^(-1) + D_S A3'(C1'A1')^(-1) = F3'`;
- the passive variables by definition.

Only the determinant-unit hypotheses on `A1'` and `C1' A1'` are used for the
first two cancellations.

## Inverse-Then-Forward Check

Starting from target variables, the forward map recovers:

- `C1''` because `(C1'' (A1')^(-1)) A1' = C1''`;
- `F2''` because `-(A1')^(-1) (-A1'F2'') = F2''`;
- `C^(S+1)` because
  `(C^(S+1)-A3'F2'') - A3'(A1')^(-1)(-A1'F2'') = C^(S+1)`;
- `F3''` because
  `(F3'' + D_S A3'(C1'')^(-1)) - D_S A3'(C1'')^(-1) = F3''`;
- the passive variables by definition.

Only the determinant-unit hypotheses on `A1'` and `C1''` are used.

## Block-Difference Check

The existing one-step block-elimination theorem says

```text
[1 0; -D_S A3'(C1'A1')^(-1) 1]
  ([C1' 0; 0 D_S] [A1' A2'; A3' A4'])
[1 -(A1')^(-1)A2'; 0 1]

= [C1'A1' 0; 0 D_S(A4' - A3'(A1')^(-1)A2')].
```

If an accumulated lower unitriangular multiplier contains `F3'`, multiplying
by the new lower factor changes it to

```text
F3'' = F3' - D_S A3'(C1'A1')^(-1).
```

Writing `F2'' = -(A1')^(-1)A2'`, the endpoint triangular product has the form

```text
[1 0; F3'' 1] T [1 F2''; 0 1]
  = [C1'' 0; 0 D_S C^(S+1)].
```

Subtracting the rank-model block and transporting by these triangular factors
gives the displayed p. 13 block

```text
C1'' - Er,   -F2'',   -F3'',   D_S C^(S+1) - F3'' F2''.
```

In the full suffix iteration, the lower-right block is the product
`prod_s C^(s)`, so this is the source of the displayed
`prod_s C^(s) - F3 F2` term.

## Boundary Checks

- If `r=0`, the determinant-unit matrices are `0 x 0`; the formulas collapse
  to the passive/residual variables and use no illegal inverse.
- If a residual dimension is zero, the corresponding rectangular matrix
  spaces are empty, and the formulas remain well-typed.
- If `L=1`, there is only one residual step; the old product `D_S` is the
  endpoint identity block in the suffix-state model.
- Singular `D_S` is allowed.  The formulas never use `D_S^(-1)`.

## Lean Plan

Implement a small algebraic coordinate-change slice in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`:

```text
ProductReductionStepRawCoordinates
ProductReductionStepChartCoordinates
ProductReductionStepRawCoordinates.toChart
ProductReductionStepChartCoordinates.toRaw
productReductionStepCoordinate_left_inverse
productReductionStepCoordinate_right_inverse
```

The inverse theorems should be used on the determinant-chart domains.  The
structure-level block-difference theorem is deferred to the next wrapper slice;
it should reuse `productReduction_chartLocalInductionStep_fromBlocks_indexed`
and `triangularBlockProductDifference_fromBlocks_indexed`.

## Nonclaims

This does not prove exact-rank or source-rank openness, analytic coordinate
chart status, chart coverage, analytic germ transport, Jacobian/prior
compatibility, regular-coordinate RLCT additivity, normal crossings, pole
order, or RLCT extraction.
