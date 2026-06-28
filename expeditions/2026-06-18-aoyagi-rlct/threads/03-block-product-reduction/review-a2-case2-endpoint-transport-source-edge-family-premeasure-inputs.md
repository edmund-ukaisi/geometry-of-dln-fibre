# Review - A2 Case 2 endpoint-transport source-edge-family pre-measure inputs

Date: 2026-06-28.

Reviewer: xhigh `Mill`.

Verdict: PASS.

## Checks

- The theorem correctly specializes the generic source-family pre-measure bridge
  with `M := 1`, aligning `Fin 3` endpoints and `Fin 2` edges.
- The endpoint orientation is correct: `case2PostPivotTwoEdgeDomain` has
  endpoint `0 = τ`, endpoint `1 = residual columns`, and endpoint
  `Fin.last 2 = residual rows`; the residual-coordinate equivalence therefore
  uses `(e (Fin.last 2)).symm` for rows and `((e 0).symm.trans eNext)` for
  columns.
- The proof is finite plumbing: it supplies determinant-chart and stored-`C`
  residual-factor readouts from the endpoint-transported Case 2 lemmas and then
  delegates to the generic source-family bridge.
- Placement in `RetainedPassiveCase2LocalJacobianMeasure.lean` is appropriate:
  the generic `RetainedPassiveLocalMeasure.lean` remains Case2-free, while this
  wrapper lives in the Case 2 leaf bridge.
- The reproduction, statement card, and ledgers accurately state the result and
  preserve the nonclaim boundary.

The review was read-only and did not rerun Lean.  The controller focused builds,
hygiene checks, and axiom-footprint probe are recorded in the thread and theorem
ledger.
