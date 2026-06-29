# Statement Card - A2 retained-passive source-edge-family source-stratum continuous-density two-sided iff

Date: 2026-06-29.

## Claim

For the concrete retained-passive source-edge-family chart-produced measure,
continuity and positivity of the transported density at `(base,0)` produce a
smaller regular-coordinate radius `R <= Rmax` and constants

```text
0 < d_rho,
0 <= D_rho,
```

such that the source-stratum density comparison bounds

```text
d_rho <= density(x,u),
density(x,u) <= D_rho
```

hold eventually on `nhdsWithin base sourceStratum` for `u in Metric.ball 0 R`.
With residual boundedness explicitly supplied at that produced radius and with
the two loss comparison bounds supplied at `Rmax`, there is an open
neighborhood `U` such that actual loss-density integrability over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

is equivalent to residual negative-power integrability on the same restricted
source-rank stratum:

```text
residualNegPowerIntegrableOn (fun E => E) (U inter sourceStratum) mu t.
```

## Lean Artifacts

Files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main helper:

```text
exists_pos_radius_le_eventually_nhdsWithin_density_two_sided_bounds_of_continuousAt_pos
```

Main theorem:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density
```

## Proved

- A positive continuous real density at `(base,0)` has positive lower and
  finite upper bounds after shrinking the regular-coordinate radius below any
  prescribed positive cap.
- The relative-neighborhood version of that helper gives source-stratum
  eventual density bounds.
- The lower and upper loss comparison bounds supplied at `Rmax` restrict to
  the produced `R`.
- The retained-passive source-edge-family chart-produced source-stratum
  two-sided iff applies with the produced `R`, `d_rho`, and `D_rho`.

## Assumed

- `[SFinite nu]` and `nu.IsAddHaarMeasure`.
- Retained-data a.e. measurability for the unweighted selected-entry signed
  box.
- Determinant-chart membership and the retained source-readback residual-
  factor identity through the banked retained-passive source-edge-family
  theorem.
- `0 < Rmax`, `0 < t`, and positive lower/upper loss comparison constants.
- Continuity and positivity of the transported density at `(base,0)`.
- The two source-stratum loss comparison bounds at radius `Rmax`.
- Residual boundedness `residualSquareSum <= R^2` on the chart-produced
  measure restricted to the retained-passive local source, where `R` is the
  produced radius.

## Cited

None in this theorem.

## Deferred

No proof of residual boundedness at the produced radius; no proof of the loss
comparison bounds; no selected-entry critical-integrability proof; no
signed-box source/image equality; no source-rank coverage; no source-prior,
Jacobian, or density transport; no original-loss identification; no normal
crossings, pole order, or RLCT extraction.

## Status

Focused Lean builds passed for `DLNFibre.DLN.Aoyagi.LocalMeasureHandoff` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure`.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, direct axiom
probe, and Goodall the 2nd xhigh read-only review passed.  The axiom footprint
is `[propext, Classical.choice, Quot.sound]`.
