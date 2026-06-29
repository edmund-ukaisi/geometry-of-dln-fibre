# Statement Card - A2 Retained-Passive Open Punctured-Sector Readout

Status: Lean theorem landed; focused build passed; xhigh review PASS.

Reproduction:

```text
reproduction-a2-retained-passive-open-punctured-sector-readout.md
```

Review:

```text
review-a2-retained-passive-open-punctured-sector-readout.md
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean
```

## Claim

For passive selected-entry Case 2 coordinates, the open determinant-domain
source-readback package also supports a fixed-pivot selected-entry inverse
readout on the nonzero-pivot sector.  For every point `z = (theta,y)` in the
open determinant-domain neighborhood, source readback recovers the transported
retained-passive datum; if `y pivotNext != 0`, then the selected-entry inverse
of the residual readout from that source readback recovers `y`.

## Lean

```text
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq_preimageOfPivotNeZero_residualReadout_eq
```

## Proved

- The open set is the same determinant-domain neighborhood produced by
  `exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq`.
- On that open set, the fixed-base p.13 source edge family lies in the
  retained-passive local source and `sourceReadback E = retainedData z`.
- The residual-factor product of `sourceReadback E` is reindexed to the
  selected-entry center coordinates using `residualCoordEquiv`.
- The with-passive endpoint residual-factor identity rewrites this residual
  readout as `SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2`.
- On the hypothesis `z.2 pivotNext != 0`,
  `SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap` recovers
  `z.2`.

## Assumed

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of passive fields `A1passive`, `F2`, `A3passive`, `Ctop`, and
  `F3`.
- Basepoint determinant units for `Ctop z0.1` and `A1passive z0.1`.
- Fixed-base complement data `U0, hU0`.
- The pointwise nonzero-pivot hypothesis for the selected-entry inverse.

## Deferred

- Any measure equality or measure pushforward theorem.
- Determinant-chart Haar transport and external/original source-prior
  comparison.
- Selected-entry source-image equality and source-rank coverage.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource
```

Full aggregator build also passed:

```text
scripts/lb DLNFibre
```

The builds emitted only pre-existing warning noise from replayed unrelated
modules; the edited module built without new warnings after making the
theorem's nonzero-pivot conclusion binder anonymous.

`scripts/sorries`, `git diff --check`, the touched Lean-file forbidden-marker
scan, and the direct axiom probe passed.  The axiom probe reports:

```text
[propext, Classical.choice, Quot.sound]
```
