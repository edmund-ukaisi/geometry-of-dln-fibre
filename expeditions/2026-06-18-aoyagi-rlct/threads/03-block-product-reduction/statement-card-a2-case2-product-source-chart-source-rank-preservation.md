# Statement Card - A2 Case 2 product source-chart source-rank preservation

## Claim

The concrete Case 2 passive-theta endpoint source chart carries a fixed-base
product-reduction certificate whenever the retained endpoint datum is in the
determinant chart.  Under the explicit Case 2 rank equations for the base
source chart, sufficiently small p.13 regular coordinates preserve membership
in the same named source-rank stratum.

Public Lean names:

```text
case2PassiveThetaEndpointSourceChart_productReductionCertificate

exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_sourceRankStratum_of_base_rank
```

## Inputs Used

- retained-passive local-source membership for the endpoint source chart;
- the equivalence between retained-passive local-source membership and
  recursive determinant charts;
- the generic recursive-determinant-chart to product-reduction-certificate
  constructor;
- the existing Case 2 passive-theta source-rank theorem;
- the generic p.13 product-coordinate source-rank preservation theorem;
- a small-ball unit determinant fact for `ctopMatrix u`.

## Output

Lean returns `R > 0`, `R <= Rmax`, and proves that for every theta satisfying
the determinant-chart condition and the two endpoint rank equations, every
`u in ball 0 R` gives

```text
(theta, u) in
  paperEndpointFixedBaseSourceRankStratum W2 B2 productSourceChart r rEdge.
```

## Nonclaims

This is not source-rank coverage and not source-image equality.  It does not
prove original/source-prior transport, Haar/Jacobian transport, normal
crossings, pole order, or RLCT extraction.
