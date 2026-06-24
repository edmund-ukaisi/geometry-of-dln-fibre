# Statement Card - A2 source-stratum literal regular/residual square-sum

## Claim

On the source-rank stratum filter, the literal p. 13 signed/corrected
product-difference square-sum is locally mutually bounded by factor `2` with
the sum of the regular block square-sum and the residual block square-sum.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source
```

## Statement Shape

For real `PaperEndpointFixedBaseRegularCoordinateSourceData`, eventually in

```text
nhdsWithin x0 (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
```

Lean proves

```text
literalSquareSum
  <= 2 * (regularBlockSquareSum + residualBlockSquareSum)
```

and

```text
regularBlockSquareSum + residualBlockSquareSum
  <= 2 * literalSquareSum.
```

## Boundary

Finite source-side square-sum comparison only.  No analytic chart, no
Fubini/polar shift, no normal-crossing certificate construction, no pole order,
and no RLCT extraction.

## Reproduction

`reproduction-a2-source-stratum-literal-regular-residual-square-sum.md`
