# Statement Card - A2 retained-passive source-edge-family chart-produced source-stratum two-sided iff

Date: 2026-06-29.

## Claim

For the concrete retained-passive source-edge-family chart

```text
sourceChart y =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W B U0 hU0 (retainedData y),
```

the retained-data a.e. measurability, determinant-chart landing, and
source-readback residual-factor identity supply the chart measurability,
retained-passive local-source landing, and selected-entry residual readout
needed by the chart-produced source-stratum selected-entry two-sided iff.
With explicit residual boundedness on the chart-produced measure restricted to
the retained-passive local source and four explicit source-stratum two-sided
loss/density bounds, there is an open neighborhood `U` such that actual
loss-density integrability over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

is equivalent to residual negative-power integrability on the same restricted
source-rank stratum:

```text
residualNegPowerIntegrableOn (fun E => E) (U inter sourceStratum) mu t.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure
```

## Proved

- A.e. measurability of the concrete source-edge-family chart from the
  retained-data a.e. measurability hypothesis.
- Pointwise landing of that chart in the retained-passive p.13 local source.
- The selected-entry residual readout from the retained source-readback
  residual-factor identity.
- Application of the chart-produced source-stratum selected-entry two-sided
  iff.

## Assumed

- `[SFinite nu]` and `nu.IsAddHaarMeasure`.
- The retained-data a.e. measurability for the unweighted signed box.
- Determinant-chart membership for the retained data.
- The retained source-readback residual-factor identity.
- Explicit residual boundedness `residualSquareSum <= Rreg^2` on the
  chart-produced measure restricted to `localSource`.
- `0 < Rreg`, `0 < t`, positive lower comparison constants, and the four
  supplied source-stratum-filter loss/density bounds.

## Cited

None in this theorem.

## Deferred

No proof of residual boundedness or comparison bounds; no selected-entry
critical-integrability proof; no signed-box source/image equality; no
source-rank coverage; no source-prior/Jacobian/density transport; no
original-loss identification; no normal crossings, pole order, or RLCT
extraction.

## Status

Focused Lean build passed.  `scripts/sorries`, `git diff --check`, touched
Lean-file forbidden-marker scan, direct axiom probe, and Schrodinger the 2nd
xhigh read-only review passed.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.
