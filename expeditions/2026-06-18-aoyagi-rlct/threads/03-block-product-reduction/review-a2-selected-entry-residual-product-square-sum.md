# Review - A2 selected-entry residual-product square-sum

Date: 2026-06-25.

Reviewer: xhigh `Hooke`.

Verdict: pass.

## Scope Checked

The reviewer checked the current uncommitted Lean slice and expedition notes
read-only:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean
threads/03-block-product-reduction/reproduction-a2-selected-entry-residual-product-square-sum.md
threads/03-block-product-reduction/statement-card-a2-selected-entry-residual-product-square-sum.md
claims.md
priorities.md
synthesis.md
```

## Findings

No blocking findings.

The theorem

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_residualProduct_eq_matrix
```

is sound as a readout composition.  Its substantive inputs are exactly the
supplied residual-coordinate equivalence and the supplied residual-product
matrix identity.  The proof first derives pointwise coordinate readout from
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix`,
then applies
`SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_eq_residual_of_coord_readout`.

## Boundary Check

The docs and ledgers do not overclaim.  This theorem does not prove the
residual-product matrix identity, construct the residual-index equivalence,
prove source coverage, identify source measures, produce normal crossings,
compute pole order, or prove RLCT.  The matrix identity is a theorem
hypothesis, and the residual-coordinate equivalence is an argument.

## Checks

The reviewer confirmed the touched Lean file elaborates.  The controller also
ran the focused build:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure
```

and separately ran `scripts/sorries` and `git diff --check`, both clean.
