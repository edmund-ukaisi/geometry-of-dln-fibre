# Statement Card - A2 retained-passive F3 positive-tail dLast target staging

Status: reproduced; Lean proved; focused and full builds passed; independent
xhigh implementation review passed; sorry/whitespace/axiom audits passed.

## Claim

For a retained-passive tuple `z` with `0 < M` in the determinant chart and
tangent `v`, choose a terminal passive index

```text
q : Fin M,     q.succ = Fin.last M.
```

Let

```text
Dzv = d(topologyTupleEdgeRawOrder)_z(v),
XsuccF2 = retainedPassiveTargetRecoveredSuccessorF2At z Dzv.
```

The terminal top-factor derivative in the landed `F3` bridge is the passive
top tangent `v.A1passive(q)`, hence it can be replaced by the target-staged
passive `A1` expression

```text
targetLast =
  Dzv.A1passive(q)
    - XsuccF2(q.succ) * coord.solvedA3(q.succ)
    - coord.F2(q.succ.succ) * rawEdgeTupleA3(Dzv,q.succ).
```

Thus the positive-tail `F3` bridge admits the term-only substitution

```text
Dzv.F3
  - dEarly_z(v) * coord.solvedA1(Fin.last M)
  + (coord.F3 - Early(z)) * targetLast
= formal.F3.
```

Consequently,

```text
(the staged expression) * (-(coord.solvedA1(Fin.last M)))^{-1} = v.F3.
```

## Lean target

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Proposed Lean names:

```text
fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply
F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

## Assumed

The main Lean theorems assume

```text
z in topologyTupleDetChartSet.
q.succ = Fin.last M.
```

The equality `q.succ = Fin.last M` supplies the positive-tail terminal
predecessor explicitly and avoids a brittle predecessor construction.

## Dependencies

- `retainedPassiveLastTopResidualFactorProduct_eq`;
- `retainedPassiveSolvedA1_eq_of_ne_zero`;
- `RetainedPassiveNonredundantCoordinateData.A1seed_succ`;
- `A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive`;
- `F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.

## Review

Initial read-only xhigh scouts `Avicenna`, `Kepler`, and `Gibbs` agreed on the
scope and warned not to merge current `origin/dev` before this narrow Aoyagi
slice.  Independent implementation reviewer `Raman` passed this slice.

## Cited

None.

## Deferred

The derivative recurrence for `Early`; full positive-tail `F3` target staging;
whole-tuple target-side normalization; determinant-one target-side
`LinearEquiv`; actual derivative determinant equality; measure transport;
normal crossings; pole order; RLCT.

## Kill conditions

- The theorem must not identify the terminal raw lower-left target derivative
  with zero.
- The theorem must not replace `Last` by the first passive tail.
- The target-staged replacement is for `dLast` only; `dEarly` remains explicit.
- The theorem must not claim determinant equality, determinant-one target
  shear, measure transport, normal crossings, pole order, or RLCT.
