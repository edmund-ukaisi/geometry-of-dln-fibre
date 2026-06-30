# Statement Card - A2 Case 2 Product Source-Chart Product-Reduction Certificate

## Claim

For the concrete Case 2 endpoint product source chart, a sufficiently small
p.13 regular-coordinate ball gives the fixed-base product-reduction
certificate eventually along the base source-rank filter.

Public Lean name:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_productReductionCertificate_nhdsWithin_source
```

## Inputs Used

- the generic fixed-base theorem
  `exists_pos_radius_le_productReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_nhdsWithin_source`;
- the concrete base source chart
  `case2PassiveThetaEndpointSourceChart`;
- the p.13 regular-coordinate determinant-unit small ball.

## Output

For every `Rmax > 0`, Lean returns `0 < R <= Rmax` such that eventually in

```text
nhdsWithin theta0 sourceStratum
```

every `u in ball(0,R)` satisfies

```text
PaperEndpointFixedBaseProductReductionCertificate
  W2 B2 U0 hU0 productSourceChart rEdge (theta, u).
```

## Proof Shape

Instantiate the generic fixed-base product-coordinate certificate theorem with

```text
CedgeBase = case2PassiveThetaEndpointSourceChart ...
M = 0
```

and unfold the local `let`s used by the concrete Case 2 theorem.

## Nonclaims

No source-rank coverage, no source-image equality, no original/source-prior
transport, no Haar/Jacobian transport, no normal crossings, no pole order, and
no RLCT extraction is proved.
