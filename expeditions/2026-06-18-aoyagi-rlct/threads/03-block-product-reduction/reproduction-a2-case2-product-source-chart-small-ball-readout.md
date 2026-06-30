# Reproduction - A2 Case 2 product source chart small-ball readout

Date: 2026-06-30.

Status: pen-and-paper check for the local small-ball version of the concrete
p.13 product-coordinate readout.

## Question

The pointwise product-chart readout needs

```text
IsUnit (det (ctopMatrix u)).
```

Can this be packaged as a radius condition `u in ball 0 R` for the concrete
Case 2 product source chart?

## Calculation

The generic regular-suspension API already proves:

```text
exists_pos_radius_le_regular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily_nhdsWithin_source
```

For any source-dependent base family `CedgeBase`, it returns `R > 0`, with
`R <= Rmax`, such that eventually along the base source-rank stratum and for
all `u in ball 0 R`,

```text
regular(productFamily(x,u)) = u
residual(productFamily(x,u)) = residual(CedgeBase x).
```

The radius is obtained from the elementary determinant fact that `ctopMatrix 0`
is the identity block, hence `ctopMatrix u` remains a determinant unit for
small `u`.

Specialize again to

```text
alpha = Case2PassiveTheta
CedgeBase = case2PassiveThetaEndpointSourceChart W2 B2 n hS hcont hnext hU0 eNext e
M = 0.
```

Then the returned source stratum is the Case 2 passive-theta source stratum

```text
paperEndpointFixedBaseSourceRankStratum W2 B2 sourceChart r rEdge,
```

and the product chart is the full p.13 chart

```text
productSourceChart(theta,u).
```

Thus, after shrinking `R`, the coordinate readouts are valid uniformly for all
small regular variables `u` and eventually in `theta` along the source stratum.

## Boundary

This theorem still does not prove that the product chart image covers a
source-neighborhood, nor does it define a full readback from edge families to
`(theta,u)`.  The eventual filter is along the supplied base source-rank
stratum.  The theorem is a local coordinate readout, not a source-prior or Haar
transport theorem.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq_nhdsWithin_source
```

The proof should specialize the generic small-ball theorem with `M := 0` and
the concrete passive-theta endpoint source chart.

## Nonclaims

No full inverse/readback to `(theta,u)`, no source-image coverage, no original
or external source-prior transport, no Haar transport, no normal crossings, no
pole order, and no RLCT extraction.
