# Review - A2 Retained-Passive Open Punctured-Sector Readout

Date: 2026-06-29.

Status: PASS.

Reviewed artifacts:

```text
reproduction-a2-retained-passive-open-punctured-sector-readout.md
statement-card-a2-retained-passive-open-punctured-sector-readout.md
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean
```

Reviewer: `Anscombe the 3rd`, xhigh read-only Lean/API review.

## Findings

No blocking findings.

The theorem

```text
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq_preimageOfPivotNeZero_residualReadout_eq
```

matches the reviewed passive-variable sector frontier.  It states the combined
with-passive open punctured-sector inverse/readout package requested by
`reproduction-a2-retained-passive-passive-variable-sector-transport.md` and
`statement-card-a2-retained-passive-passive-variable-sector-transport.md`.

The statement is honest: it produces an open set `U`, local-source membership,
`sourceReadback E = retainedData z`, and, only under
`z.2 pivotNext != 0`, the selected-entry preimage of the residual readout
equals `z.2`.  The theorem has no measure, Haar, source-prior, source-image,
source-rank, normal-crossing, pole-order, or RLCT conclusion, and the docstring
explicitly excludes those claims.

The proof uses the intended ingredients:

- `exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq`
  supplies the open set and source-readback equality.
- The with-passive endpoint residual-factor chart-map identity rewrites the
  residual-factor product of the readback.
- `residualCoordEquiv.symm` reindexes the residual coordinates back to the
  selected-entry center.
- `SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap` closes
  the punctured fixed-pivot inverse.

The reviewer found no import, scope, API, or proof-fragility blocker.  The
controller had already run the focused build:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource
```

which passed; the only replayed warnings were pre-existing warnings from
`ProductReductionStepRegularDensity`.

Post-review controller checks also passed: `git diff --check`,
`scripts/sorries`, the touched Lean-file forbidden-marker scan, and a direct
axiom probe.  The new theorem's axiom footprint is
`[propext, Classical.choice, Quot.sound]`.

The full `DLNFibre` aggregator build also passed via `scripts/lb DLNFibre`;
the output contained only pre-existing warning noise from replayed unrelated
modules.
