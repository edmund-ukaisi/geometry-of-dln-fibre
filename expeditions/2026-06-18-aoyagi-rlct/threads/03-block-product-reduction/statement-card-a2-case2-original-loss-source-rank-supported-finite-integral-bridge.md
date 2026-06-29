# Statement Card: A2 Case 2 original-loss source-rank-supported finite-integral bridge

## Status

Proved in Lean locally.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.
Independent xhigh review is recorded separately.

## Statement

For the endpoint-transported explicit continuing Case 2 selected-entry source
chart, assume the hypotheses of the endpoint-basis original-loss finite-
integral bridge.  Also assume the explicit source-rank support equations:

```text
rank(total base product) = r,
r + card(tau) = rEdge 0,
forall yNext, r + rank(successor selected-entry matrix yNext) = rEdge 1.
```

Then there exist `R`, `C`, and an open neighborhood `U` of the base edge family
such that

```text
0 < R, R <= Rmax, 0 <= C,
```

and the endpoint-basis original square-Frobenius `lossDLN` has finite
negative-power regular-coordinate integral over

```text
(mu.restrict U).prod nu.
```

## Lean Declaration

```text
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_restrict_open_of_sourceRankSupport
```

## Proves

- The source-stratum restriction in the final product measure can be removed
  after assuming the explicit rank equations that support the chart-produced
  measure on `sourceStratum`.
- The original-loss target, endpoint bases, density, exponent, and radius
  bookkeeping are unchanged from the source-stratum theorem.

## Assumed

- all hypotheses of the source-stratum endpoint-basis original-loss theorem;
- `Module.finrank R (range (paperTotalMap W2 B2)) = r`;
- `r + card tau = rEdge 0`;
- `forall yNext, r + rank(case2SuccessorSelectedEntryMatrix ... yNext) =
  rEdge 1`.

## Cited

None.  This is measure-support bookkeeping over existing Lean theorems.

## Deferred

No source-rank coverage theorem, selected-entry source/image equality, external
source-prior transport, Jacobian comparison for such a prior, normal-crossing
construction, pole-order calculation, or RLCT extraction is proved.

## Route

Call the source-stratum original-loss finite-integral theorem, use the existing
Case 2 support theorem to prove `mu.restrict sourceStratum = mu`, rewrite
`mu.restrict (U inter sourceStratum)` as `mu.restrict U`, and reuse the finite
integral.
