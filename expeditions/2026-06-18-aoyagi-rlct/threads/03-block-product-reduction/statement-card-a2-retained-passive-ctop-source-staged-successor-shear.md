# Statement Card - A2 Retained-Passive Ctop Source-Staged Successor Shear

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

## Lean Names

```text
Ctop_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

## Reproduction

```text
reproduction-a2-retained-passive-ctop-source-staged-successor-shear.md
```

## Claim

For a retained-passive determinant-chart point `z` and tangent `v`, the actual
raw-order derivative's first top-left component agrees with the
point-specialized formal raw-order Jacobian after replacing the successor `F2`
derivative and the multiplied successor lower-left derivative by explicit
staged source tangents:

```text
Dzv.Ctop
  - X_F(0) * coord.solvedA3_0
  - coord.F2_1 * X_G(0)
  - d(Tail^{-1})_z(v) * coord.Ctop
= formal(z)(v).Ctop.
```

The passive-tail inverse derivative term remains explicit in the statement.

## Proof Plan

1. Start from the previously proved derivative-staged bridge
   `Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
2. Rewrite `d(coord.F2_1)_z(v)` using
   `fderiv_retainedPassive_toCoordinateData_F2_succ_apply`.
3. Rewrite
   `coord.F2_1 * d(coord.solvedA3_0)_z(v)` using
   `retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3`.
4. Leave the derivative of `Tail^{-1}` as the explicit `fderiv` term.

## Status

Implemented in Lean.  Focused build has passed.  Independent xhigh review
passed.  Full `DLNFibre` build, `scripts/sorries`, `git diff --check`, and
axiom audit passed.  The Lean theorem depends only on
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

This is not full `Ctop` source staging because the passive-tail inverse
derivative is not expanded.  It is not a fully source-staged tuple, target-side
`LinearEquiv`, determinant-one shear, determinant equality, measure theorem,
normal-crossing theorem, pole-order theorem, or RLCT theorem.
