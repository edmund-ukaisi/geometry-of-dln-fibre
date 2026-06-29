# Review - A2 retained-passive source-stratum chart-produced selected-entry two-sided loss-density iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-retained-passive-source-stratum-chart-produced-selected-entry-two-sided-loss-density-iff.md
statement-card-a2-retained-passive-source-stratum-chart-produced-selected-entry-two-sided-loss-density-iff.md
```

## Controller Review

Pass with boundary.

The theorem removes only the arbitrary-measure signed-box pushforward
hypothesis from the retained-passive source-stratum-bound selected-entry
two-sided iff.  It defines the measure as the selected-entry weighted
signed-box pushforward and proves the retained-passive local-source restriction
equality from pointwise chart landing.

Residual readout, residual boundedness over the chart-produced measure
restricted to the retained-passive local source, and all four source-stratum
loss/density comparison bounds remain explicit.  The theorem does not assume
selected-entry critical inequalities, positive signed-box radii,
source-density upper/nonnegativity hypotheses, residual integrability, signed-
box source/image equality, source-rank coverage, source-prior transport,
normal crossings, pole order, or RLCT.

## Xhigh Review

Helmholtz the 2nd passed the theorem surface.

The review confirmed that the wrapper defines only `signedBox`,
`sourceMeasure`, `mu`, and `localSource`; derives a.e. measurability for the
weighted source measure by absolute continuity of `withDensity`; proves only

```text
mu.restrict localSource = Measure.map sourceChart sourceMeasure;
```

and then delegates to the already banked source-stratum-bound theorem.

The review also confirmed that `hle_source` is stated over the chart-produced
measure restricted to `localSource`, that the loss/density hypotheses remain
on `paperEndpointFixedBaseSourceRankStratum`, and that the pointwise
`hchart_mem` hypothesis is safely promoted to an a.e. statement by
`Filter.Eventually.of_forall`.

## Hygiene

Passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

Passed:

```text
scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan passed.  Direct axiom probe for
the new theorem returned `[propext, Classical.choice, Quot.sound]`.
