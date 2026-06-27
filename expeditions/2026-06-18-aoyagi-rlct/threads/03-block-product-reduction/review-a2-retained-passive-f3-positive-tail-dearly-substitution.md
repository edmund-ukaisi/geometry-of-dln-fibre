# Review - A2 retained-passive F3 positive-tail dEarly substitution

Date: 2026-06-27.

Reviewer: xhigh `Sartre`.

Status: PASS.

## Verdict

No blocking mathematical or indexing-fidelity findings.

The Lean theorems

```text
F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

correctly substitute the first-index zero-current `dEarly` formula into the
positive-tail `F3` bridge whose terminal `dLast` factor was already
target-staged, and then recover the source `F3` tangent from the same staged
expression.

## Checks

- The theorem is parameterized by positive tail `M+1`, with source type
  `Fin ((M+1)+2)` and tuple parameter `RetainedPassiveRawTopologyTuple
  (M := M+1)`.
- The first earlier-tail index is the zero branch:

```text
q0 = 0 : Fin (M+1),
p0 = q0.castSucc,
r0 = q0.succ.
```

- The terminal `dLast` index is

```text
qLast = Fin.last M : Fin (M+1),
qLast.succ = Fin.last (M+1).
```

- The theorem uses
  `fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply`,
  not the successor-current theorem.
- The factor order is preserved:

```text
Dzv.F3
  - dEarly * coord.solvedA1(Fin.last (M+1))
  + (coord.F3 - Earlyfun z) * dLast_target.
```

- The terminal `dLast` target expression is unchanged from the previous slice.
- `dPsucc`, `dTail`, and `(fderiv Nextfun z) v` remain explicit.
- The recovery theorem consumes the equality theorem and
  `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`; it right-multiplies
  the staged expression by
  `(-(coord.solvedA1 (Fin.last (M+1))))^-1` and does not expand `dEarly`.

## Scope

This slice is a narrow consumer rewrite plus its formal recovery companion.  It does not prove full
positive-tail `F3` target staging, does not expand `dPsucc`, `dTail`, or the
successor early tail, and proves no determinant equality, measure transport,
normal crossings, pole order, or RLCT.
