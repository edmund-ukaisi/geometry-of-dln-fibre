# Reproduction - A2 Case 2 Product Source-Chart Local-Source Support

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is one-way support for the
constructed product source chart inside the named retained-passive p.13 local
source.

## Question

The local-measure theorems use the named set

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource
```

as the support set for retained-passive p.13 source points. The product source
chart already has readout and certificate wrappers. Does the constructed
product point itself lie in this named local source?

## Calculation

The retained-passive local source is equivalent to the recursive determinant
chart predicate:

```text
x in paperEndpointFixedBaseRetainedPassiveP13LocalSource
  iff
paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts x.
```

For the explicit p.13 product-coordinate edge family, the generic product
reduction certificate theorem gives

```text
PaperEndpointFixedBaseProductReductionCertificate
```

whenever `det(Ctop(u))` is a unit. Its `detCharts` field is exactly the
recursive determinant chart predicate required by the local-source iff.

Thus, for

```text
CedgeProd =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    ... CedgeBase,
```

we have

```text
(x,u) in paperEndpointFixedBaseRetainedPassiveP13LocalSource ... CedgeProd.
```

Specializing `CedgeBase` to the concrete Case 2 endpoint source chart and
then unfolding the local-source preimage gives the source-side statement

```text
productSourceChart(theta,u)
  in paperEndpointFixedBaseRetainedPassiveP13LocalSource ... (fun E => E).
```

Finally, the determinant-unit small ball around `u = 0` removes the explicit
`det(Ctop(u))` hypothesis and gives the source-filter theorem along
`nhdsWithin theta0 sourceStratum`.

## Lean Targets

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_retainedPassiveP13LocalSource
case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source
```

## Nonclaims

This proves support for the constructed product chart only. It does not prove
source-rank coverage, source-image equality, original/source-prior transport,
Haar/Jacobian transport, normal crossings, pole order, or RLCT extraction.
