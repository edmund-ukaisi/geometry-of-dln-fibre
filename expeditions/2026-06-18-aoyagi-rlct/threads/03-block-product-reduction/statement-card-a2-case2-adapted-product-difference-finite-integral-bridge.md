# Statement Card: A2 Case 2 adapted product-difference finite-integral bridge

## Status

Proved in Lean locally.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.
Independent xhigh review is recorded separately.

## Statement

For the endpoint-transported explicit continuing Case 2 selected-entry source
chart, assume fixed-base source data, positive selected-entry radii, the
selected-entry critical inequality, and a regular-coordinate density continuous
and positive at `(base, 0)`.

Then there exist `R`, `C`, and an open neighborhood `U` of the base edge family
such that

```text
0 < R, R <= Rmax, 0 <= C,
```

and the adapted p.13 product-difference square-sum has finite negative-power
regular-coordinate integral over

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

## Lean Declaration

```text
exists_radius_open_lintegral_ofReal_adaptedProductDifferenceSquareSum_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
```

## Proved

- The lower comparison

  ```text
  c * (residualSq + regularSq) <= adaptedProductDifferenceSquareSum
  ```

  is derived from the source-coordinate product-reduction theorem, not supplied
  as a hypothesis.
- The density nonnegativity and upper bound are derived by shrinking from
  positive continuity at `(base, 0)`.
- The selected-entry residual positivity and negative-power integrability
  remain supplied by the existing Case 2 chart-produced source-measure theorem.

## Assumed

- endpoint equivalences `eNext` and `e`;
- fixed-base source data for the identity edge-family source map;
- `nu.IsAddHaarMeasure`;
- `0 < Rmax`, `0 < t`;
- positive signed-box radii `Rres`;
- selected-entry critical inequality
  `2 * t < #(center.erase pivotNext) + 1`;
- continuous positive density at `(base, 0)`.

## Cited

None.  This is Aoyagi-specific finite coordinate and local-measure
bookkeeping.

## Deferred

No original-loss identification, reverse finite-integral implication,
source-rank support rewrite, selected-entry source/image equality, external
source-prior or Jacobian transport, normal-crossing construction, pole-order
calculation, or RLCT extraction is proved.

## Route

Use the density-shrink lemma on the source-rank stratum; apply the
self-base multi-edge product-coordinate adapted lower-bound theorem at the
shrunk radius; then call the existing Case 2 source-stratum chart-produced
finite-integral theorem with the loss specialised to
`paperEndpointFixedBaseAdaptedProductDifferenceSquareSum`.
