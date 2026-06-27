# Review - A2 retained-passive actual derivative Ctop shear bridge

Reviewer: xhigh read-only implementation reviewer `Bohr the 5th`.

Status: PASS.

The reviewer found no blocking formalization or mathematical inaccuracies in
the Ctop shear bridge.

Checks:

- The Lean statement subtracts `dF2 * solvedA3 0`,
  `F2 * d(solvedA3 0)`, and `d(Tail^{-1}) * Ctop`, with RHS
  `Tail^{-1} * v.Ctop`, matching the reproduction note.
- The theorem uses the full successor `F2` slot
  `coord.F2 (0 : Fin (M + 1)).succ`, not a stored nonterminal-only field.
- The multiplication order is correct: `dF2 * solvedA3`,
  `F2 * d(solvedA3)`, and `dTailInv * Ctop`.
- The proof expands the raw component as `U * Ctop + H * G` before the
  product-rule cancellation.
- The Jacobian bridge states only the sheared `Ctop` component equality with
  `retainedPassiveFormalRawOrderJacobianAt`; it does not assert full
  derivative equality or a determinant formula.
- The reviewed files contain no `sorry`, `admit`, new `axiom`, `unsafe`, or
  evaluator shortcut.

The reviewer did not edit files.
