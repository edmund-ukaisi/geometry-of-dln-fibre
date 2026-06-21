# Statement card - A4 Case 2 source-side weighted lower-row handoff

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Expected name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_constructedSourceFreeCprimeWeightedNextSameStageProduct_withCorrectedPostData`

## Statement

For the displayed Case 2 pivot chart, the lower rows of the old source-side
weighted `Q/P` product, with the old following factor reconstructed from
`Q*Cprime`, reindex to

```text
diagonal(successor lower-row weights)
  *
(case2DisplayedPostPivotResidualBlock
  * case2DisplayedPostPivotFreeFollowingFactor).
```

The theorem also carries the existing corrected post-data projections.

## Proved

Lean-proved as the expected name above.  The theorem supplies `q`, projects
the old source-side weighted `Q/P` equality to the lower rows, rewrites the
weighted right side with the successor lower-row diagonal, and carries the
corrected post-data projections.

## Assumed

- Displayed Case 2 source-chart hypotheses.
- The existing supplied/concrete boundary data used by the local `Q/P`
  package.
- A free compatible pivot-first `Cprime`.

## Cited

- None in Lean.  This is finite matrix algebra and reindexing.

## Deferred

- Source production of `Cprime`, chart coverage, arbitrary-pivot coverage,
  full successor product, transition invariance, terminal relabeling,
  Jacobian arithmetic, normal crossings, pole order, and RLCT extraction.

## Review

- xhigh source checker `Maxwell` accepted this as a narrow projection of the
  constructed-source free-`Cprime` local product, with the precision condition
  that the source-side product includes the `P_q` row operation.
- xhigh Lean API scout `Noether` typechecked the theorem shape and proof via
  `lake env lean --stdin`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `lake build DLNFibre` passed.
- `lake env lean DLNFibre.lean` passed.
- `scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
