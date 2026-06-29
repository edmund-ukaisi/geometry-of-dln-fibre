# Review - A2 retained-passive chart-produced selected-entry two-sided loss-density iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-retained-passive-chart-produced-selected-entry-two-sided-loss-density-iff.md
statement-card-a2-retained-passive-chart-produced-selected-entry-two-sided-loss-density-iff.md
```

## Controller Review

Pass with boundary.

The theorem removes only the arbitrary-measure signed-box pushforward
hypothesis from the retained-passive local-source selected-entry two-sided iff.
It defines the measure as the selected-entry weighted signed-box pushforward
and proves the local-source restriction equality from pointwise chart landing.

Residual readout, residual local boundedness, and all four two-sided
loss/density comparison bounds remain explicit.  The residual boundedness
hypothesis is stated over the chart-produced measure restricted to the
retained-passive local source.

The theorem does not assume selected-entry critical inequalities, positive
signed-box radii, source-density upper/nonnegativity hypotheses, residual
integrability, source coverage, source-rank coverage, source-prior transport,
normal crossings, pole order, or RLCT.

## Xhigh Review

Carver the 2nd passed the theorem surface.

The review confirmed that the wrapper defines the chart-produced measure,
derives a.e. measurability under the weighted source measure by absolute
continuity, and derives the retained-passive local-source restriction equality
from pointwise chart landing.  It leaves residual boundedness and all four
two-sided local loss/density bounds explicit.

The review also confirmed that the residual boundedness hypothesis is stated
over the chart-produced measure restricted to the retained-passive local
source, that the conclusion is the intended iff over that same restricted
source, and that no `[SFinite mu]` or hidden critical-integrability/source-
coverage assumptions are introduced.

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
