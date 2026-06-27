# Statement Card - A2 retained-passive dPcast successor solvedA1 substitution

Status: Lean proved; xhigh review passed.

## Claim

At a tuple determinant-chart point, specialize the solved-`A1` residual-product
derivative to a successor current factor `p = q.succ` and substitute the
successor solved-`A1` derivative:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(q.succ)
    + Psucc(z) * v.1 q.
```

The derivative of the successor product `Psucc` remains explicit.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Planned Lean name:

```text
fderiv_retainedPassive_solvedA1_residualFactorProduct_succ_castSucc_apply
```

## Verification

Focused builds passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and the theorem
axiom audit reported only `[propext, Classical.choice, Quot.sound]`.

Review:

```text
review-a2-retained-passive-dpcast-succ-solveda1-substitution.md
```

## Dependencies

- `fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply`;
- `fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply`;
- the determinant-chart hypothesis inherited from the generic residual-product
  product rule.

## Cited

None.

## Deferred

Any pointwise cleanup of `solvedA1_z(q.succ)`; any expansion of `dPsucc`;
downstream `dEarly` specialization or reindexing; target staging; determinant
theorem; measure theorem; normal crossings; pole order; RLCT.

## Structure & Ideas Observed

The product-rule helper already isolates the current solved-factor derivative.
For a successor current factor, that derivative is the passive source tangent
`v.1 q`; the surrounding residual-product derivative and the pointwise current
factor stay unchanged.

## Route

Use the generic solved-`A1` residual-product product-rule theorem with
`p : Fin (M+1) := q.succ`.  Then use the successor solved-`A1` derivative
theorem to rewrite only

```text
(fderiv (fun y => A1fun y p) z) v.
```

Keep `dPsucc` explicit, and keep the first summand as
`dPsucc * data.toCoordinateData.solvedA1 p`.

## Kill Conditions

- The theorem must not use `v.1 q.succ` or `v.1 p`.
- The theorem must not commute matrix factors.
- The theorem must not expand `dPsucc`.
- The theorem must not touch downstream `dEarly` wrappers in this slice.
- The theorem must not claim determinant equality, measure transport, normal
  crossings, pole order, or RLCT.
