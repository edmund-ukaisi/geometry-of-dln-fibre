# Review - A2 retained-passive local-source selected-entry two-sided loss-density iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-retained-passive-local-source-selected-entry-two-sided-loss-density-iff.md
statement-card-a2-retained-passive-local-source-selected-entry-two-sided-loss-density-iff.md
```

## Controller Review

Pass with boundary.

The theorem is a specialization of the selected-entry local-source two-sided
iff to the retained-passive local source.  It proves exactly the two
retained-passive hypotheses needed by that socket: local-source measurability
and edge-matrix measurability, both from `Continuous Cedge`.

It leaves the selected-entry signed-box pushforward identity, source-chart
a.e. measurability, residual readout, residual local boundedness, and all four
two-sided loss/density comparison bounds as explicit hypotheses.

The theorem does not assume selected-entry critical inequalities, positive
signed-box radii, source-density upper/nonnegativity hypotheses, residual
integrability, a base-point self-edge equation, source coverage, source-rank
coverage, source-prior transport, normal crossings, pole order, or RLCT.

## Xhigh Review

Halley the 2nd passed the theorem surface.

The review confirmed that the wrapper discharges only retained-passive
local-source measurability and edge-matrix measurability.  The signed-box
pushforward identity, residual readout, residual boundedness, and four
two-sided loss/density bounds remain explicit.

The review also confirmed that the theorem does not introduce `[SFinite mu]`
or depend on a base-point self-edge equation, selected-entry critical
inequalities, positive signed-box radii, source-density upper/nonnegativity
hypotheses, residual integrability, source coverage, source-stratum transport,
normal crossings, pole order, or RLCT.

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
