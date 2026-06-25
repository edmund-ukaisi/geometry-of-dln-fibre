# Review - A2 selected-entry chart-image local handoff

Date: 2026-06-25.

## Verdict

Accepted.

The reviewer found no mathematical fidelity issue.  The wrapper specializes the
local-source selected-entry signed-box theorem to the concrete finite chart
image

```text
source = chartMap pivot '' signedBoxSet Rres,
sourceChart = chartMap pivot,
mu = volume.
```

The source-measurability input is discharged by
`SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet`,
chart a.e.-measurability by continuity of `chartMap`, and the measure identity
by the finite selected-entry weighted pushforward theorem, used in the
orientation required by the local-source handoff.

## Scope Check

The local loss and density assumptions are stated over
`nhdsWithin x0 (chartMap pivot '' signedBoxSet Rres)`, and the conclusion
integrates over

```text
volume.restrict (U ∩ chartMap pivot '' signedBoxSet Rres).
```

Thus the theorem remains a finite chart-image wrapper.  It does not identify
the chart image with the original p.13 DLN source, prove source coverage or
original-source measure equality, compare the full DLN loss, produce normal
crossings, compute pole order, or extract RLCT.

## Verification

The reviewer typechecked
`lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean`.  The
controller also verified the focused Lake target with the worktree-local shared
store:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure
```
