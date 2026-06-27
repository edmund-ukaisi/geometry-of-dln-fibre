# Statement Card - A2 retained-passive F3 positive-tail dEarly substitution

Status: Lean proved; xhigh review passed.

## Claim

For a positive retained-passive tail, parameterized as `M+1`, the terminal
`F3` bridge with the terminal `dLast` factor already target-staged can also
consume the first-index `dEarly` derivative formula.

Use

```text
q0 = 0 : Fin (M+1),
p0 = q0.castSucc,
r0 = q0.succ,
qLast = Fin.last M : Fin (M+1).
```

The theorem substitutes

```text
(fderiv Earlyfun z) v = dEarly_expanded
```

where `dEarly_expanded` is exactly the RHS of
`fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply`.
The resulting `F3` expression is

```text
Dzv.F3
  - dEarly_expanded * coord.solvedA1(Fin.last (M+1))
  + (coord.F3 - Earlyfun(z)) * dLast_target
  = formal.F3.
```

Here `dLast_target` is the previously staged terminal top-factor derivative:

```text
Dzv.A1(qLast)
  - XsuccF2(qLast.succ) * coord.solvedA3(qLast.succ)
  - coord.F2(qLast.succ.succ) * rawA3(Dzv,qLast.succ).
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean names:

```text
F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

## Verification

Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and both theorem
axiom audits reported only `[propext, Classical.choice, Quot.sound]`.

Review:

```text
review-a2-retained-passive-f3-positive-tail-dearly-substitution.md
```

## Dependencies

- `F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`;
- `fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply`;
- endpoint identity `(Fin.last M).succ = Fin.last (M+1)`.

## Cited

None.

## Deferred

Expansion of `dPsucc`, recursive expansion of `dTail`, expansion of
`dCnext`, iteration of `Nextfun`, full positive-tail `F3` target staging,
target-side `LinearEquiv`, determinant equality, measure transport, normal
crossings, pole order, and RLCT.

## Kill Conditions

- The first earlier-tail index must be `0 : Fin (M+1)`.
- The terminal `dLast` index must be `Fin.last M : Fin (M+1)`.
- Preserve the noncommutative order inside `dEarly_expanded`.
- Preserve the outer multiplication `- dEarly_expanded * coord.solvedA1(Fin.last (M+1))`.
- Do not simplify terminal products or claim a final `F3` target staging theorem.
