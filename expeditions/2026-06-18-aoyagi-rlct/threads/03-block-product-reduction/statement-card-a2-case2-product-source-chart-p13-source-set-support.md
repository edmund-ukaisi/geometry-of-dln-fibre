# Statement Card - A2 Case 2 product source chart p.13 source-set support

## Claim

For the concrete Case 2 full p.13 product source chart, there is a positive
regular-coordinate radius `R <= Rmax` such that, eventually along the base
source-rank stratum and for every `u in ball 0 R`, the product chart lies in
the named p.13 source edge-family set.

The corresponding pushed-forward small-ball product measure is supported on
that named p.13 source edge-family set.

Public Lean names:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_p13SourceEdgeFamilySet_nhdsWithin_source

exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_p13SourceEdgeFamilySet_eq_self
```

## Inputs Used

- the concrete passive-theta endpoint source chart;
- a base point `theta0`;
- a source-rank stratum `paperEndpointFixedBaseSourceRankStratum ... r rEdge`;
- a positive radius cap `Rmax`;
- the existing retained-passive local-source small-ball support theorem;
- the existing retained-passive local-source measure-support theorem;
- the identity-map specialization of
  `paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet`.

## Output

Lean returns `R > 0`, `R <= Rmax`, and eventual source-set membership:

```text
eventually theta in nhdsWithin theta0 sourceStratum,
  forall u in ball 0 R,
    productSourceChart(theta,u) in p13SourceSet.
```

The measure version returns an open neighborhood `V` of `theta0` and proves:

```text
Measure.map productSourceChart productDomainMeasure
```

is unchanged after restriction to the named p.13 source edge-family set,
provided the source stratum is measurable and the product chart is a.e.
measurable for the small-ball product-domain measure.

## Proof Shape

Apply the retained-passive local-source versions, then rewrite local-source
membership and local-source measure restriction by

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet
```

with the edge-family map specialized to the identity.

## Nonclaims

This is not source-image coverage and not a full product-chart inverse.  It
does not prove original/source-prior transport, Haar transport, normal
crossings, pole order, or RLCT extraction.
