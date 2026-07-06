# A2 Case 2 lossDLN concrete inverse-density restrict-open wrapper

## Source calculation

The concrete p.13 inverse-density finite-integral theorem produces an open
neighborhood `U` of `base` and proves finiteness over

```text
(mu.restrict (U cap sourceStratum)).prod nu.
```

For the endpoint-transported selected-entry source chart, the existing support
theorem says that the chart-produced measure `mu` is already supported on the
source-rank stratum when the rank identities are supplied:

```text
mu.restrict sourceStratum = mu.
```

Therefore, for open `U`,

```text
mu.restrict (U cap sourceStratum)
  = (mu.restrict sourceStratum).restrict U
  = mu.restrict U.
```

Substituting this equality into the finite integral gives the restrict-open
version.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_restrict_open_of_sourceRankSupport
```

## Boundary

This is only a support-restriction wrapper around the concrete inverse-density
finite-integral theorem.  It does not prove source-rank coverage, identify an
external/original prior, prove raw-Haar or source/product-coordinate transport,
construct normal crossings, compute pole order, or extract RLCT.
