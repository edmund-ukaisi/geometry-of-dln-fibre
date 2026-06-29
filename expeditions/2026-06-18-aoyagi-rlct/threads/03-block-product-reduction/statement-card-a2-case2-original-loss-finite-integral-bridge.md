# Statement Card: A2 Case 2 original-loss finite-integral bridge

## Status

Proved in Lean locally.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.
Independent xhigh review is recorded separately.

## Statement

For the endpoint-transported explicit continuing Case 2 selected-entry source
chart, assume fixed-base source data, supplied endpoint bases, positive
selected-entry radii, the selected-entry critical inequality, and a
regular-coordinate density continuous and positive at `(base, 0)`.

Then there exist `R`, `C`, and an open neighborhood `U` of the base edge family
such that

```text
0 < R, R <= Rmax, 0 <= C,
```

and the original endpoint square-Frobenius `lossDLN` has finite negative-power
regular-coordinate integral over

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

The `lossDLN` target is the endpoint chain map of the fixed base network in the
supplied endpoint bases, and the input tuple is `chainMapMatrixTuple b` applied
to the chart-produced product-coordinate edge family.

## Lean Declaration

```text
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
```

## Proves

- The regular-plus-residual lower comparison for original `lossDLN` is derived
  by composing the adapted product-difference lower-bound theorem with the
  finite endpoint-basis comparison.
- Density nonnegativity and an upper bound are derived by shrinking from
  positive continuity at `(base, 0)`.
- The result is for the chart-produced selected-entry source measure and the
  supplied endpoint bases.

## Assumed

- endpoint equivalences `eNext` and `e`;
- fixed-base source data for the identity edge-family source map;
- endpoint bases `b`;
- `nu.IsAddHaarMeasure`;
- `0 < Rmax`, `0 < t`;
- positive signed-box radii `Rres`;
- selected-entry critical inequality
  `2 * t < #(center.erase pivotNext) + 1`;
- continuous positive density at `(base, 0)`.

## Cited

None.  The endpoint comparison is finite basis-change linear algebra already
formalised in Lean.

## Deferred

No reverse finite-integral implication, source-rank support rewrite,
selected-entry source/image equality, external source-prior transport,
Jacobian comparison for such a prior, normal-crossing construction, pole-order
calculation, or RLCT extraction is proved.

## Route

Use the density-shrink lemma on the source-rank stratum; apply the self-base
multi-edge product-coordinate adapted lower-bound theorem at the shrunk
radius; compose it with the endpoint-basis comparison to get a lower bound for
`lossDLN`; then call the existing Case 2 source-stratum chart-produced
finite-integral theorem with `loss = originalLoss`.
