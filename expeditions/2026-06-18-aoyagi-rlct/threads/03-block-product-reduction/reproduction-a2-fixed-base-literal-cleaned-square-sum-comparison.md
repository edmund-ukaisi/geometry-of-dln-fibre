# Reproduction - A2 fixed-base literal-cleaned square-sum comparison

Date: 2026-06-24.

Status: pen-and-paper reproduced; real fixed-base finite comparison formalised
in Lean.

## Target

The previous fixed-base source-data slice proves that near the base chain the
actual p. 13 `F2` and `F3` regular-coordinate blocks satisfy

```text
squareSum(F2_x) + squareSum(F3_x) <= 1.
```

The finite comparison slice already proves that under this hypothesis the
literal signed/corrected p. 13 coordinate square-sum and the cleaned
coordinate square-sum are mutually bounded by a factor `2`.  This note records
the fixed-base specialisation to the actual suffix-state coordinate maps.

## Fixed-Base Cleaned and Literal Families

For a fixed-base suffix state `S(x)`, the cleaned p. 13 scalar coordinate
family is

```text
value (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D.
```

The literal signed/corrected family attached to the product-difference block is

```text
literalValue (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D.
```

This is the scalar family for

```text
fromBlocks X (-F2) (-F3) (D - F3 * F2)
```

with

```text
X  = S.Ctop - 1,
F2 = -(S.B),
F3 = lowerLeftBlock S.L,
D  = S.D.
```

The sign convention is important: the cleaned `F2` variable in the existing
p. 13 coordinate map is `-(S.B)`, so the literal family uses
`literalValue ... (-(S.B)) ...`, not `literalValue ... S.B ...`.

## Factor-Two Comparison

From

```text
sourceData :
  PaperEndpointFixedBaseRegularCoordinateSourceData
    W B U0 hU0 x0 Cedge H r rEdge
```

over `real`, the fixed-base smallness theorem gives eventually in `nhds x0`
the required hypothesis

```text
squareSum(-(S.B)) + squareSum(lowerLeftBlock S.L) <= 1.
```

At each such point, apply the two finite comparison theorems:

```text
literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one
coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
```

with `X = S.Ctop - 1`, `F2 = -(S.B)`, `F3 = lowerLeftBlock S.L`, and
`D = S.D`.  This yields eventually

```text
squareSum(literal fixed-base coordinates)
  <= 2 * squareSum(cleaned fixed-base coordinates)
```

and

```text
squareSum(cleaned fixed-base coordinates)
  <= 2 * squareSum(literal fixed-base coordinates).
```

The same two inequalities hold in the source-rank `nhdsWithin` filter by
filter weakening from the ambient theorem.

## Boundary

This is finite real square-sum comparison for the actual fixed-base scalar
coordinate maps.  It does not identify analytic generator ideals, prove chart
coverage, prove analytic coordinate status, prove source-rank openness, build
a regular-suspension normal-crossing certificate, compute pole order, or
extract RLCT.
