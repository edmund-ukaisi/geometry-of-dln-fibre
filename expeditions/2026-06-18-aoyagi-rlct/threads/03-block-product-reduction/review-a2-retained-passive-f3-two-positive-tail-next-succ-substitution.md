# Review - A2 retained-passive F3 two-positive-tail next-successor substitution

Date: 2026-06-27.

Reviewers: xhigh `Dirac`; xhigh `Jason`.

Status: PASS.

No mathematical or formalisation findings.

## Checks

The Lean theorem

```text
F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

is scoped to tail length `(M+1)+1`.  It instantiates the prior positive-tail
`F3` first-index theorem with `M := M+1`, and instantiates the successor
`dEarly` theorem with `M := M+1` and `s0 : Fin (M+1)`.

The successor tangent is correctly `v.1 u1`, not `v.1 q1`.  The nested
successor contribution preserves the noncommutative order

```text
Cprod1 * A3p1 * Pcast1^-1 * (...) * Pcast1^-1.
```

## Scope

The docs and ledgers accurately keep the result narrow: no one-positive-tail
claim, no first-level `dPsucc` rewrite, no terminal cleanup, no full `F3`
target staging, and no determinant equality, measure transport, normal
crossings, pole order, or RLCT.

## Recovery Companion Check

Jason's xhigh review passed the recovery theorem

```text
F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

The theorem is exactly a recovery companion for the same two-positive-tail
staged expression: it composes the staged equality theorem with
`retainedPassiveFormalRawOrderJacobianAt_recovers_F3` and right-multiplies by
`(-(coord.solvedA1 (Fin.last ((M+1)+1))))^-1`.  The proof does not add a
determinant, measure, normal-crossing, pole-order, or RLCT claim.

The indexing check passed: `q0/p0/r0` and `s0/q1/u1/p1/r1` match the
statement card, and the successor tangent remains `v.1 u1`, not `v.1 q1`.
