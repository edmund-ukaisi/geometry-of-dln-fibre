# Review - A2 retained-passive actual derivative F3 shear bridge

Reviewer: xhigh read-only explorer `Jason the 5th`.

Status: PASS.

The reviewer found no active Lean proof blocker and no mathematical orientation
issue in the F3 bridge.

Checks:

- The terminal solved lower-left block is differentiated as
  `-(F3 - Early) * LastTop`, so the final tangent term is
  `v.F3 * (-LastTop)`.
- The multiplication order is right multiplication by the terminal square
  factor.  This is forced by the matrix shapes and matches the formal
  raw-order terminal component.
- The sign handling is consistent: `Matrix.neg_mul` rewrites the raw solved
  block, while `Matrix.mul_neg` identifies the target as `dF3 * (-LastTop)`.
- The `M = 0` endpoint is handled by the one-edge terminal product lemma:
  `LastTop = coord.solvedA1 (Fin.last M) = coord.Ctop`, not `1`.
- `LastTop` is distinct from the first-edge passive `Tail` used by the `Ctop`
  bridge.

Implementation notes handled by the controller:

- The derivative proof warning at the local `hraw_apply` step was changed from
  `simpa [hFL_apply]` to `simp [hFL_apply]`.
- The Jacobian wrapper qualifies the `ChartLocalSuffixState` helper names
  explicitly and rewrites the terminal residual factor using
  `retainedPassiveLastTopResidualFactorProduct_eq`.

The reviewer did not edit files.  The controller subsequently ran focused
local builds for both derivative and Jacobian modules.
