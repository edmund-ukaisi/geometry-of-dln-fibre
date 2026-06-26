# Review - A2 Retained-Passive Solved A1 Derivative

Date: 2026-06-26.

Reviewer: Nietzsche the 4th, xhigh read-only explorer.

## Verdict

No blocking issues.

## Checks

The reviewer verified that

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
```

passed.  They also ran `scripts/lb DLNFibre` and `git diff --check`; both
passed, with only pre-existing unrelated linter warnings in the full build.

## Findings

The derivative file stays within the intended checkpoint:

```text
differentiableAt_retainedPassiveA1TailAfterFirst
differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
```

plus coordinate-projection differentiability helpers.  It does not claim full
raw-order differentiability, a determinant/Jacobian formula, density, measure
pushforward, normal crossings, pole order, or RLCT.

The finite hypotheses are acceptable: projection lemmas expose `Finite`
hypotheses and create local `Fintype` instances using `Fintype.ofFinite`;
determinant/inverse/product lemmas keep `Fintype rho` and `DecidableEq rho`
where square matrix determinants and inverses require them.

The use of `DifferentiableAt.mul` is valid in this checkpoint because both
current multiplication sites are square `Matrix rho rho Real` products.
Heterogeneous matrix multiplication remains future work for the lower-left and
raw-order derivative layers.

## Follow-Up

The reviewer initially flagged import ordering in `lean/DLNFibre.lean` as a
low style issue.  The controller moved the new import to the end of the import
list before banking the checkpoint.

