# Statement Card: A2 Case 2 endpoint-transport continuous-density small-box two-sided iff

## Status

Proved in Lean locally.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.
Independent xhigh review is recorded separately.

## Statement

For the endpoint-transported explicit continuing Case 2 selected-entry source
chart, positive continuity of the regular-coordinate density at `(base, 0)`
produces `R dρ Dρ` with

```text
0 < R, R <= Rmax, 0 < dρ, 0 <= Dρ.
```

For any `delta` satisfying

```text
0 <= delta,
forall i : center, Rres i <= delta,
delta^2 * (1 + #(center.erase pivotNext) * delta^2) <= R^2,
```

there is an open `U` containing the base edge family such that actual
loss-density finiteness over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

is equivalent to residual negative-power integrability over
`U inter sourceStratum` for the same chart-produced measure `mu`.

## Lean Declaration

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density_of_smallBox
```

## Inputs Kept Explicit

- endpoint equivalences `eNext` and `e`;
- fixed-base source data;
- `[SFinite nu]` and `nu.IsAddHaarMeasure`;
- positive `Rmax`, `cLreg`, `CLreg`, and `t`;
- positive continuity of `density` at `(base, 0)`;
- lower and upper source-stratum loss comparison bounds at `Rmax`;
- the final `delta` and signed-box radius bounds at the produced radius `R`.

## Discharged Inputs

The theorem constructs internally:

- the concrete endpoint-transported retained-passive datum;
- its determinant-chart proof;
- the Case 2 residual-coordinate equivalence;
- the selected-entry center-matrix residual-factor readout;
- determinant-chart a.e. measurability from continuity.

## Nonclaims

No positive signed-box radius hypothesis or selected-entry critical inequality
is used.  No residual bound at `Rmax` is transported to a smaller radius.  No
source-rank coverage, source/image equality, original source-prior transport,
Jacobian comparison, normal-crossing construction, pole-order calculation, or
RLCT extraction is proved.
