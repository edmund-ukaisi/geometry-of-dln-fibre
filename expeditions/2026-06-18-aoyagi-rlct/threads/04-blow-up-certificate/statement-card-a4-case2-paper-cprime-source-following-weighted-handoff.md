# Statement card - A4 Case 2 paper-Cprime source-following weighted handoff

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Expected name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData`

## Statement

For Aoyagi's displayed Case 2 pivot chart, specialize the source-side weighted
lower-row handoff to the paper transported following factor
`C' = Q^-1 C`.  The lower rows of the old source-side weighted `Q/P` product
reindex to

```text
diagonal(successor lower-row weights)
  *
(case2DisplayedPostPivotResidualBlock
  * case2SourceFollowingFactor at (S,J+1)).
```

The theorem also carries the existing corrected post-data projections.

## Proved

Lean-proved as the expected name above.  The theorem supplies `q`, projects
the paper source-side weighted `Q/P` equality to the lower rows, rewrites the
weighted right side with the successor lower-row diagonal, identifies the
free post-pivot tail of the paper `C'` with the next same-stage source
following factor, and carries the corrected post-data projections.

## Assumed

- Displayed Case 2 source-chart hypotheses.
- The existing supplied/concrete boundary data used by the source-chart `Q/P`
  package.
- A source-coordinate following factor `C : ℕ → τ → R`.

## Cited

- None in Lean.  This is finite matrix algebra and reindexing.

## Deferred

- Full source production of `C'^(S+1)`, chart coverage, arbitrary-pivot
  coverage, successor chart-family construction, chart-produced
  recurrence/exponent post-data, transition invariance, terminal relabeling,
  Jacobian arithmetic, normal crossings, pole order, and RLCT extraction.

## Review

- xhigh A4 scout `Tesla` recommended this as the next Lean-sized A4 slice,
  provided the name does not overclaim full source production.
- xhigh source checker `Rawls` accepted the calculation after a wording fix
  about the common chart factor `u_{S,J+1}`.
- xhigh Lean API scout `Lorentz` typechecked the theorem shape via
  `lake env lean --stdin`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `lake build DLNFibre` passed.
- `lake env lean DLNFibre.lean` passed.
- `scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
