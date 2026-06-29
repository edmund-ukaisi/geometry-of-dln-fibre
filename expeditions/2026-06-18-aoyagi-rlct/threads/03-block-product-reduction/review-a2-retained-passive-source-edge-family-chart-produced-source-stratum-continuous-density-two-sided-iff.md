# Review - A2 retained-passive source-edge-family source-stratum continuous-density two-sided iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean helper:

```text
exists_pos_radius_le_eventually_nhdsWithin_density_two_sided_bounds_of_continuousAt_pos
```

Lean theorem:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-continuous-density-iff.md
statement-card-a2-retained-passive-source-edge-family-chart-produced-source-stratum-continuous-density-two-sided-iff.md
```

## Controller Review

Pass with boundary.

The helper is the expected elementary topological shrink: it chooses
`density(base,0) / 2` and `density(base,0) + 1`, uses continuity at `(base,0)`
and the product-neighborhood basis, and then restricts to `nhdsWithin`.

The retained-passive wrapper removes only the two density comparison
hypotheses from the banked source-edge-family chart-produced source-stratum
two-sided iff.  It does not remove the residual boundedness premise: the
conclusion produces `R` first and then asks for residual boundedness at that
same radius before returning the local `iff`.  This is the correct direction,
because a bound at `Rmax` would not imply a bound at the smaller produced
radius.

The two loss comparison hypotheses are still explicit, but they may be stated
at `Rmax`; the proof restricts them to `R` using the metric ball inclusion from
`R <= Rmax`.

## Xhigh Review

Goodall the 2nd passed the theorem surface.

The review confirmed that the new helper proves a positive lower bound
`d <= density`, not just nonnegativity; that the retained-passive wrapper
returns produced `R dρ Dρ` and keeps residual boundedness explicit at
`R^2`; that density bounds are discharged only from `ContinuousAt` and
positivity; and that loss bounds remain explicit at `Rmax` and are only
restricted to `R`.

No line-specific concerns were reported.

## Hygiene

Focused builds passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

Passed:

```text
scripts/sorries
git diff --check
touched Lean-file forbidden-marker scan
direct axiom probe
```

The direct axiom probe returned `[propext, Classical.choice, Quot.sound]` for
both the relative density helper and the retained-passive continuous-density
two-sided wrapper.
