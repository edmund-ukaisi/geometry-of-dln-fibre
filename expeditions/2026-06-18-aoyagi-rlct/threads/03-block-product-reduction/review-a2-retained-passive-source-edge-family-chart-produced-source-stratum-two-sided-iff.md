# Review - A2 retained-passive source-edge-family chart-produced source-stratum two-sided iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-iff.md
statement-card-a2-retained-passive-source-edge-family-chart-produced-source-stratum-two-sided-iff.md
```

## Controller Review

Pass with boundary.

The theorem is a concrete retained-passive source-edge-family wrapper around
the chart-produced source-stratum selected-entry two-sided iff.  It discharges
only source-chart a.e. measurability, retained-passive local-source landing,
and the selected-entry residual readout from retained-passive source-edge-
family data.

Residual boundedness over the chart-produced measure restricted to
`localSource`, `[SFinite nu]`, `nu.IsAddHaarMeasure`, and all four
source-stratum loss/density comparison bounds remain explicit.  The theorem
does not assume selected-entry critical inequalities, positive signed-box
radii, source-density upper/nonnegativity hypotheses, residual integrability,
signed-box source/image equality, source-rank coverage, source-prior
transport, normal crossings, pole order, or RLCT.

## Xhigh Review

Schrodinger the 2nd passed the theorem surface.

The review confirmed that the signature keeps `[SFinite nu]`, explicit
`nu.IsAddHaarMeasure`, residual boundedness, and the four source-stratum
bounds without adding `hRres`, critical inequalities, source-density bounds,
source-image/prior/Jacobian facts, normal crossings, or RLCT assumptions.

The review also confirmed that source-chart a.e. measurability is obtained by
composing retained-data a.e. measurability with the measurable retained-passive
p.13 source chart, that chart landing and source-readback residual-factor
equality are obtained through the intended source-edge-family lemma, and that
the final call is to the banked chart-produced source-stratum two-sided iff.

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
