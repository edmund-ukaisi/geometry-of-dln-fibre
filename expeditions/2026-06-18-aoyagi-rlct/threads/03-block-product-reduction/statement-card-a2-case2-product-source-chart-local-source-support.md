# Statement Card - A2 Case 2 Product Source-Chart Local-Source Support

## Claim

The explicit p.13 product-coordinate chart, and in particular the concrete
Case 2 endpoint product source chart, lands in the named retained-passive p.13
local source after shrinking the regular coordinates.

Public Lean names:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_retainedPassiveP13LocalSource

case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource

exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source
```

## Inputs Used

- the generic product-coordinate certificate theorem
  `paperEndpointFixedBaseProductReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean`;
- the local-source characterization
  `mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts`;
- the determinant-unit small-ball theorem for `ctopMatrix`;
- the concrete Case 2 endpoint source chart.

## Output

Pointwise generic form:

```text
(x,u) in paperEndpointFixedBaseRetainedPassiveP13LocalSource ... CedgeProd
```

when `det(Ctop(u))` is a unit.

Concrete Case 2 source-side form:

```text
productSourceChart(theta,u)
  in paperEndpointFixedBaseRetainedPassiveP13LocalSource ... (fun E => E)
```

under the same determinant-unit hypothesis.

Small-ball source-filter form:

```text
exists R, 0 < R <= Rmax and eventually in nhdsWithin theta0 sourceStratum,
  u in ball(0,R) ->
    productSourceChart(theta,u) in retainedPassiveP13LocalSource.
```

## Proof Shape

Use the product-coordinate certificate theorem with a dummy `rEdge`; the
certificate's `detCharts` field discharges the local-source iff. The Case 2
pointwise wrapper is a specialization and an unfolding of the source-side
identity map. The small-ball wrapper applies the determinant-unit radius and
then the pointwise Case 2 theorem.

## Nonclaims

No source-rank coverage, no source-image equality, no original/source-prior
transport, no Haar/Jacobian transport, no normal crossings, no pole order, and
no RLCT extraction is proved.
