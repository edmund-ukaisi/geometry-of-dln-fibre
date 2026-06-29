# Statement Card: A2 Case 2 source-stratum-supported continuous-density small-box two-sided iff

## Status

Proved in Lean locally.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.

## Lean Declaration

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_of_smallBox_restrict_open_of_sourceRankSupport
```

## Statement

Assume the endpoint-transported continuing Case 2 selected-entry source chart
and the explicit uniform rank support equations:

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
forall yNext,
  r + rank(case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) = rEdge 1.
```

Then the positive-continuous-density small-box source-stratum iff can be
stated over `mu.restrict U` and `residualNegPowerIntegrableOn ... U mu t`,
where `U` is the returned open neighborhood of the base source edge family.

The theorem still returns `R dρ Dρ` first, and the small-box `delta` condition
is checked at the produced radius `R`.

## Inputs Kept Explicit

- endpoint equivalences `eNext` and `e`;
- fixed-base source data;
- the three uniform source-rank support equations;
- `[SFinite nu]` and `nu.IsAddHaarMeasure`;
- positive `Rmax`, `cLreg`, `CLreg`, and `t`;
- positive continuity of the density at `(base, 0)`;
- lower and upper source-stratum loss comparison bounds at `Rmax`;
- the final `delta` and signed-box radius bounds at the produced radius `R`.

## Nonclaims

The support equations are assumptions, not coverage theorems.  This does not
prove selected-entry source/image equality, exact-rank openness, original
source-prior transport, Jacobian comparison, normal-crossing construction,
pole-order calculation, or RLCT extraction.
