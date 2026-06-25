# Review - A2 selected-entry residual-factor readout boundary

Date: 2026-06-25.

Reviewers: xhigh source scout `Kant`, xhigh Lean/API scout `Kuhn`, and
controller Lean check.

## Scope

Reviewed the new finite residual-product theorem:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  paperEndpointFixedBaseResidualProduct_eq_selectedEntryCenter_matrix_of_residualFactorProduct_eq_matrix
```

and the reproduction
`reproduction-a2-selected-entry-residual-factor-readout-boundary.md`.

## Verdict

Accepted for the stated boundary.

The theorem does not claim selected-entry source/image equality and does not
realize an arbitrary terminal matrix.  It requires:

- a compatible residual-factor family `Cfac`;
- proofs that the fixed-base transformed Schur residual blocks read as those
  factors;
- a factor-product identity identifying the ordered product with the
  selected-entry coordinate matrix;
- the residual-index equivalence.

This is the correct p.13-shaped residual socket: Aoyagi's residual object is
an ordered product through intermediate residual factors.

## Nonclaims

No compatible factor construction, no factor-product proof, no residual-index
equivalence construction, no source chart, no source/image equality, no
source-measure transport, no normal crossings, no pole order, and no RLCT.

## Checks

Focused check passed:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean
```

Post-recovery full gates passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
scripts/sorries
git diff --check
```
