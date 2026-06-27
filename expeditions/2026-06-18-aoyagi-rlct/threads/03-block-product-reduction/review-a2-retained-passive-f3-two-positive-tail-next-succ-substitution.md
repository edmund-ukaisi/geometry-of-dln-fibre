# Review - A2 retained-passive F3 two-positive-tail next-successor substitution

Date: 2026-06-27.

Reviewer: xhigh `Dirac`.

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
