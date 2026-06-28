# Review - A2 retained-passive endpoint transport

Date: 2026-06-28.

Reviewer: xhigh `Kierkegaard`.

Verdict: PASS.

## Checks

- Product transport orientation is correct.  The endpoint equivalence
  `e : κ j ≃ κ' j` is used old-to-new, transported factors are pulled back by
  `(e _).symm`, and the final product is pulled back by `(e j).symm` and
  `(e i).symm`.
- Retained-passive field transport is correctly oriented for `F2`,
  `A3passive`, `C`, and `F3`.  The determinant-chart preservation theorem is
  appropriately definitional because `detChart` only reads `Ctop` and
  `A1passive`.
- The Case 2 transported theorem uses the correct residual-coordinate
  equivalences: `(e (Fin.last 2)).symm` for rows and
  `(e 0).symm.trans eNext` for columns.
- The reproduction, statement card, and ledger language accurately keep the
  result to finite endpoint algebra and do not claim `edgeMatrix`,
  `sourceReadback`, fixed-base local-source, measure, normal-crossing,
  pole-order, or RLCT results.

The review was read-only and did not rerun Lean.  The controller build and
hygiene checks are recorded in the thread and ledgers.
