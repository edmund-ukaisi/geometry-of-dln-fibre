# Review - A2 retained-passive F3 three-positive-tail next-next successor substitution

Date: 2026-06-27.

Reviewers: xhigh `Parfit the 2nd`; xhigh `Carson the 2nd`.

Status: PASS.

No mathematical or formalisation findings.

## Pre-Lean Index Check

Parfit checked the reproduction and statement card against the existing
two-positive-tail theorem and the successor-index derivative helper.

The proposed three-positive-tail indices are correct:

```text
t0 = 0 : Fin (M+1)
s1 = t0.succ : Fin ((M+1)+1)
q2 = s1.succ
u2 = s1.castSucc
p2 = q2.castSucc
r2 = q2.succ
```

The helper must be instantiated at `s1`, not at `t0`; `t0` only defines the
second successor source parameter.  The successor branch tangent is `v.1 u2`,
not `v.1 q2`, because the helper uses `u := s.castSucc` and
`u.succ = q.castSucc = p`.

Parfit also checked that the target does not overclaim: it substitutes only
`(fderiv NextNextfun z) v`, leaves the next derivative explicit, and does not
claim determinant equality, measure transport, normal crossings, pole order,
RLCT, or full positive-tail `F3` target staging.

## Lean Fidelity Check

Carson reviewed the landed Lean theorems:

```text
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

The statements use tail length `((M+1)+1)+1` and the second successor block
`t0/s1/q2/u2/p2/r2`.  The second successor branch uses

```text
Psucc2 z * v.1 u2
```

and never `v.1 q2`.  The noncommutative factor order is preserved as

```text
Cprod2 * A3p2 * Pcast2^-1 * (...) * Pcast2^-1.
```

The recovery theorem uses the same staged expression as the equality theorem,
right-multiplies by
`(-(coord.solvedA1 (Fin.last (((M+1)+1)+1))))^-1`, and the proof depends on
the staged equality plus `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.

## Scope

The result is a narrow staged derivative bridge.  It does not rewrite
`dPsucc`, `dPsucc1`, or `dPsucc2`; it does not recurse into `dNext2`; it does
not simplify terminal or empty-suffix cases; and it does not distribute or
commute the outer product `- dEarly * terminalSolvedA1`.

No determinant equality, measure transport, normal crossings, pole order, RLCT,
or full positive-tail `F3` target staging is claimed.
