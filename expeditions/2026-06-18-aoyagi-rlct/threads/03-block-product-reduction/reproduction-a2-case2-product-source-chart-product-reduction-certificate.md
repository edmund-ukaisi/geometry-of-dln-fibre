# Reproduction - A2 Case 2 Product Source-Chart Product-Reduction Certificate

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is a concrete Case 2 wrapper
around the fixed-base p.13 product-coordinate certificate.

## Question

The Case 2 product source-chart readout package shows that, for small regular
coordinates `u`, the chart

```text
productSourceChart(theta, u)
```

has the expected regular-coordinate readout, residual-coordinate readout, and
source-readback fields. Do we also have the p.13 product-reduction
certificate for this same constructed product chart?

## Calculation

The generic fixed-base theorem

```text
exists_pos_radius_le_productReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_nhdsWithin_source
```

applies to any base edge-family map `CedgeBase`. It chooses a radius `R` from
the determinant-unit neighborhood of

```text
Ctop(u) = I + regular Ctop coordinates.
```

For every base point `x` and every `u` with `u` in `ball(0,R)`, the explicit
multi-edge product-coordinate edge family satisfies

```text
PaperEndpointFixedBaseProductReductionCertificate
```

at `(x,u)`. In the Case 2 specialization, take

```text
x = theta
CedgeBase = case2PassiveThetaEndpointSourceChart
productSourceChart =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    ... CedgeBase.
```

The theorem is stated along

```text
nhdsWithin theta0 sourceStratum,
```

but the generic proof is pointwise after choosing the small determinant-unit
radius. The source filter is retained because it is the consumer shape used by
the surrounding source-rank and local-measure theorems.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_productReductionCertificate_nhdsWithin_source
```

## Nonclaims

The theorem proves a product-reduction certificate for the constructed product
chart. It does not prove source-rank coverage, source-image equality,
source-prior transport, Haar/Jacobian transport, normal crossings, pole order,
or RLCT extraction.
