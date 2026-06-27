# Review - A2 retained-passive actual derivative passive A1 shear bridge

Reviewer: xhigh read-only implementation reviewer `Nash the 5th`.

Status: PASS.

The reviewer found no blocking formalization or mathematical inaccuracies in
the passive A1 shear bridge.

Checks:

- The index convention is correct: passive `A1passive p` corresponds to edge
  `p.succ`, and the correction terms use the successor full-`F2` slot
  `p.succ.succ` together with `coord.solvedA3 p.succ`.
- The terminal passive top-left case is covered by the `F2full` convention:
  if `p` is the last passive index, then `p.succ.succ` is the terminal zero
  full-`F2` slot.
- The product-derivative signs and matrix order are correct.  The proof
  expands `d(A + H*G)` as `dA + H*dG + dH*G` and subtracts `dH*G` and
  `H*dG`, leaving the stored passive tangent `v.1 p`.
- The proof explicitly reduces `coord.solvedA1 p.succ` to the stored passive
  variable by using `retainedPassiveSolvedA1_eq_of_ne_zero` with
  `Fin.succ_ne_zero p`.
- The formal raw-order bridge is correctly matched: the formal apply formula
  leaves the first raw tuple component unchanged, so the passive top-left
  component is `v.1 p`.
- The exposition and Lean docstrings keep the theorem scoped as a sheared
  passive-component bridge, not a global determinant, measure, normal-crossing,
  pole-order, or RLCT statement.

Non-blocking note handled before this review artifact was written:

- The reproduction note status now records that the independent xhigh check
  passed and that the Lean target was implemented.

The reviewer did not edit files and did not rerun Lean.
