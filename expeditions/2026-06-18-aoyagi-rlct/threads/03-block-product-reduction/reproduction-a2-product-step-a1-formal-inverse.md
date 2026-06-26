# Reproduction - A2 product-step A1 formal inverse

Date: 2026-06-26.

Status: pen-and-paper reproduction before Lean.

## Question

The existing one-step p. 13 coordinate inverse theorems are stated on the raw
and chart determinant domains.  Those domains are the right analytic/chart
objects, but the record-level formal inverse calculation uses only the
invertibility of the retained block `A1`.

This slice separates the finite algebraic inverse cancellation from the
determinant-chart and regular-expression hypotheses.

## Source Anchors

Aoyagi Lemma 2 and Theorem 3, PDF pp. 10-13.  The relevant source-backed
content is the elementary block coordinate change used in the p. 13 product
reduction.  This note does not use the quiver paper.

The source formulas are represented in Lean as raw variables

```text
(C1, D, F3old, A1, A2, A3, A4)
```

and chart variables

```text
(Ctop, D, A1, A3, F2, F3, C).
```

The forward coordinate map is

```text
Ctop = C1 A1,
D    = D,
A1   = A1,
A3   = A3,
F2   = - A1^{-1} A2,
F3   = F3old - D A3 (C1 A1)^{-1},
C    = A4 - A3 A1^{-1} A2.
```

The inverse coordinate map is

```text
C1    = Ctop A1^{-1},
D     = D,
F3old = F3 + D A3 Ctop^{-1},
A1    = A1,
A2    = - A1 F2,
A3    = A3,
A4    = C - A3 F2.
```

## Pen-and-paper Calculation

For `toRaw (toChart x)`, substitute the forward formulas into the inverse.
The `C1` coordinate becomes

```text
(C1 A1) A1^{-1} = C1
```

using only that `A1` is invertible.  The `A2` coordinate becomes

```text
- A1 ( - A1^{-1} A2 ) = A1 A1^{-1} A2 = A2,
```

again using only invertibility of `A1`.  The `F3old` coordinate cancels by
additivity:

```text
(F3old - D A3 (C1 A1)^{-1}) + D A3 (C1 A1)^{-1} = F3old.
```

The `A4` coordinate is

```text
(A4 - A3 A1^{-1} A2) - A3 ( - A1^{-1} A2 ) = A4.
```

The passive coordinates `D`, `A1`, and `A3` are definitionally unchanged.
No inverse of `D` appears.  The only determinant-unit cancellation needed is
right/left cancellation by `A1`; the totalized inverse of `C1 A1` appears in
the `F3old` expression on both sides and cancels additively.

For `toChart (toRaw y)`, the `Ctop` coordinate is

```text
(Ctop A1^{-1}) A1 = Ctop,
```

using only that `A1` is invertible.  The `F2` coordinate is

```text
- A1^{-1} ( - A1 F2 ) = F2.
```

For `F3`, first the previous line rewrites the recomputed top block
`(Ctop A1^{-1}) A1` to `Ctop`; then

```text
(F3 + D A3 Ctop^{-1}) - D A3 Ctop^{-1} = F3.
```

The residual coordinate is

```text
(C - A3 F2) - A3 (-F2) = C.
```

Thus the formal inverse law on both sides only requires `det A1` to be a unit.

## Lean Shape

Add two record-level finite algebra theorems:

```text
productReductionStepCoordinate_left_inverse_of_isUnit_A1
productReductionStepCoordinate_right_inverse_of_isUnit_A1
```

The existing determinant-chart theorems should remain as wrappers, because
the determinant chart is still the right source/target domain for the p. 13
coordinate map as a chart and for later derivative and measure statements.

## Nonclaims

- No weakening of the determinant-chart domain for the analytic chart map.
- No local inverse for the original DLN parameter space.
- No source-rank coverage or source/image equality.
- No source-measure pushforward, density/Jacobian identity, normal crossings,
  pole order, or RLCT extraction.
