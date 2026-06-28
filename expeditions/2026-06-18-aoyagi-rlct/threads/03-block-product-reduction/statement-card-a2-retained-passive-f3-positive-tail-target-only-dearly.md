# Statement Card - A2 F3 positive-tail target-only dEarly

## Lean Names

Expected in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

## Mathematical Content

For a positive retained-passive tail, this replaces the source-staged recursive
lower-left derivative in the terminal `F3` bridge by the target-only lower-left
derivative:

```text
dEarly# =
  retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt (M := M) hz Dzv 0.
```

The proved branch has the same shape as the existing recursive `dEarly` bridge:

```text
Dzv.F3
  - dEarly# * solvedA1(last)
  + (F3_z - Early_z) * dLast#
= formal.F3.
```

The recovery theorem right-multiplies the same displayed branch by
`(-solvedA1(last))^-1` to recover the source `F3` tangent.

## Dependencies

```text
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
```

## Non-Claims

This is not a target-side linear equivalence, determinant-one normalizer,
Jacobian determinant equality, source-prior transport, inverse-density
pushforward, normal crossings, pole order, RLCT, or analytic extraction.
