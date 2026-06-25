# Review - A2 selected-entry residual-product matrix readout

Date: 2026-06-25.

Reviewer: Plato, xhigh independent checker.

Verdict: PASS.

## Scope

Reviewed the Lean theorem
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix`
in `SelectedEntryOriginalLossLocalMeasure.lean`, plus the reproduction and
statement card for the residual-product matrix readout bridge.

## Findings

No mathematical findings.

The Lean theorem assumes both the residual-index equivalence and the
residual-product matrix identity, then applies
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct` and
`AoyagiResidualBlockCoordinateIndex.value_matrix`.  It proves exactly the
pointwise `hresidual_readout` shape consumed by the selected-entry
original-loss wrapper.

The source boundary is correct: the theorem does not construct `CedgeBase`,
prove the residual-product matrix identity, construct the residual-index
equivalence, prove source coverage, transport source measure, produce normal
crossings, compute pole order, or extract RLCT.

Low wording issues were fixed after review:

- the statement-card verification command now says it is run from `lean/`;
- the reproduction now says a later calculation "supplies" the matrix identity;
- the thread note now says the theorem reduces the residual-readout subgoal,
  not future source work as a whole.

## Verification

Reviewer read-only checks:

- `cd lean && LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`
- `git diff --check`

Controller verification:

- `env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure`

