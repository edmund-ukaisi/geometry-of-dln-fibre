# Reproduction - A2 source-stratum literal regular/residual square-sum split

Date: 2026-06-24.

Status: pen-and-paper reproduced; formalised in Lean.

## Target

The p. 13 Fubini-facing loss shape should be the literal full block loss
compared with

```text
regular square-sum + residual square-sum.
```

The previous finite source-data theorem compared the literal p. 13 square-sum
with the cleaned product-difference square-sum.  The cleaned square-sum had
already been split as the sum of the regular block coordinate square-sum and
the residual block coordinate square-sum.  This slice composes those two facts.

## Calculation

For real fixed-base source data, the already formalised local comparison says
eventually on the source-rank stratum

```text
literalSquareSum <= 2 * cleanedSquareSum,
cleanedSquareSum <= 2 * literalSquareSum.
```

The cleaned fixed-base map is a disjoint sum:

```text
productDifferenceCoordinateMap
  = Sum.elim regularBlockCoordinateMap residualBlockCoordinateMap.
```

Therefore finite square-sum additivity for disjoint sums gives

```text
cleanedSquareSum
  = regularBlockSquareSum + residualBlockSquareSum.
```

Substitution yields the desired source-stratum eventual comparison:

```text
literalSquareSum
  <= 2 * (regularBlockSquareSum + residualBlockSquareSum),

regularBlockSquareSum + residualBlockSquareSum
  <= 2 * literalSquareSum.
```

## Lean Target

The theorem is in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source
```

It uses:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source

paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual
```

## Boundary

This is finite real square-sum comparison on the source-rank `nhdsWithin`
filter.  It is not source-rank openness, not analytic regular-coordinate
status, not a Fubini/polar theorem, not a regular-suspension chart
construction, and not an RLCT statement.
