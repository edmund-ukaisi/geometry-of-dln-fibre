# Statement Card - A2 cleaned coordinate square-sum

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
aoyagiCoordinateSquareSum
aoyagiCoordinateSquareSum_sumElim
AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_eq_regular_add_residual
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim
paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual
```

## Statement Shape

`aoyagiCoordinateSquareSum f` is the finite algebraic square-sum

```text
sum c, f c ^ 2.
```

For a disjoint sum of coordinate indices,

```text
aoyagiCoordinateSquareSum (Sum.elim f g)
  =
aoyagiCoordinateSquareSum f + aoyagiCoordinateSquareSum g.
```

The cleaned p. 13 product-difference coordinate index is the disjoint sum of
the regular coordinate index and the residual coordinate index.  Lean proves
that its square-sum splits accordingly:

```text
squareSum(productDifferenceValue X F2 F3 D)
  =
squareSum(regularValue X F2 F3) + squareSum(residualValue D).
```

For the fixed-base suffix-state maps, Lean also proves that the
product-difference coordinate map is exactly `Sum.elim` of the regular and
residual maps, and therefore its square-sum is the regular square-sum plus the
residual square-sum.

## Scope

Finite algebraic loss bookkeeping for the cleaned p. 13 generator family

```text
C1 - Er,   F2,   F3,   prod_s C^(s).
```

## Nonclaims

No equality with the literal signed/corrected p. 13 Frobenius square-sum,
analytic generator transport, analytic coordinate chart, local inverse,
source-rank openness, chart coverage, Jacobian/prior compatibility,
normal-crossing construction, pole order, or RLCT extraction is proved.
