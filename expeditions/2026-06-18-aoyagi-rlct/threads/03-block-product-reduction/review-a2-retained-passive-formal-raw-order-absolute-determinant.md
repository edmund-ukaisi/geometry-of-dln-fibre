# Review: A2 Retained-Passive Formal Raw-Order Absolute Determinant

Reviewer: Laplace the 5th, xhigh read-only review.

## Verdict

Accepted with no findings.

## Findings

No Lean or mathematical fidelity issues were found.

The reviewer checked that the new formal absolute determinant theorems elaborate
and that their dependency footprint is the expected theorem-proving substrate
only.
The sign erasure is sound: the proof first rewrites the signed formal
determinant theorem, takes absolute values, and then uses `Matrix.det_neg` only
to prove `|det(-A)| = |det(A)|` for the edge-local and terminal factors.

The names and docstrings keep the theorem formal-only and do not identify the
formal determinant with the analytic Frechet-derivative determinant.  The
reproduction and statement card preserve the endpoint convention
`LastTop = coord.solvedA1 (Fin.last M)` and the terminal exponent
`κ' (Fin.last (M + 1))`.

No source/PDF, source-prior transport, normal-crossing, pole-order, or RLCT
overclaim was found.

## Verification

The reviewer ran direct Lean elaboration for the two changed Lean files and a
dependency audit for the two new theorem names.  The controller additionally
ran:

- focused `lean/scripts/lb` builds for
  `DLNFibre.DLN.Aoyagi.RetainedPassiveFormalRawOrder` and
  `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`;
- full `lean/scripts/lb DLNFibre`;
- the project forbidden-marker scan;
- `git diff --check`.

All controller checks passed.
