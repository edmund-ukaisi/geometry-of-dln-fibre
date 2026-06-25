# Review - A2 finite basis-change square-sum comparison

Date: 2026-06-25.

Reviewer: Curie the 5th, xhigh.

Confirmatory review: Pasteur the 5th, xhigh, read-only.

Status: passed after uniformity hardening.

## Findings

No blockers.

The matrix estimate has the right direction for the intended later use.  From
`T = L * M * Rmat`, the existing finite Cauchy-Schwarz estimate gives
`squareSum(T) <= squareSum(L) * squareSum(Rmat) * squareSum(M)`, and choosing
`c = max(1, squareSum(L) * squareSum(Rmat))^{-1}` gives a strictly positive
constant even in degenerate finite-index cases.

The basis-change orientation is correct:

```text
[f]_{bE,bF}
  = [id_F]_{bF',bF} * [f]_{bE',bF'} * [id_E]_{bE,bE'}.
```

The original pointwise Lean theorems were mathematically valid, but the API did
not expose the fact needed downstream: the comparison constant is fixed once
the basis-change matrices are fixed, and does not vary with `f`.  This was
addressed by adding the uniform theorems

```text
exists_pos_const_forall_matrixCoordinateSquareSum_le_mul
exists_pos_const_forall_linearMap_toMatrix_squareSum_le_of_basis_change
```

alongside the pointwise wrappers.

## Boundary

This review does not certify any theorem mentioning `lossDLN`.  The remaining
loss-comparison prerequisite is still the tuple/product bridge identifying
`mult` of edge matrices in chosen bases with the endpoint chain-map matrix.

## Confirmatory Review

Pasteur independently checked the current worktree after the uniform theorem
patches.  No blockers were found.  The review confirmed the Lean orientation
`L = [id_F]_{bF',bF}`, `M = [f]_{bE',bF'}`,
`Rmat = [id_E]_{bE,bE'}` and `L * M * Rmat = [f]_{bE,bF}`; it also confirmed
that the uniform theorems quantify `∃ c` before `∀ M` and `∀ f`, respectively,
and that the notes do not claim a landed `lossDLN` bridge.
