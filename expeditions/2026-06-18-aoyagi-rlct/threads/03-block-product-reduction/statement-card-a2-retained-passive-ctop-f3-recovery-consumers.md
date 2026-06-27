# Statement Card - A2 Retained-Passive Ctop and F3 Recovery Consumers

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

## Lean Names

```text
Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
F3_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

## Reproduction

```text
reproduction-a2-retained-passive-ctop-f3-recovery-consumers.md
```

## Claim

Assume `z` lies in the retained-passive determinant chart:

```text
z in topologyTupleDetChartSet.
```

The Ctop staged expressions already proved equal to the formal Ctop component
recover the source `Ctop` tangent after left multiplication by the passive
tail:

```text
Tail * U_Ctop = v.Ctop.
```

There are separate zero-tail and positive-tail theorems.  In the positive
case, `U_Ctop` contains the first passive recurrence substitution and leaves
the suffix derivative explicit.

The F3 staged expression already proved equal to the formal F3 component
recovers the source `F3` tangent after right multiplication by the inverse of
the negative terminal solved top-left block:

```text
U_F3 * (-(coord.solvedA1 (Fin.last M)))^{-1} = v.F3.
```

## Proof Plan

1. Invoke the relevant staged component equality:
   `Ctop_tail_zero...`, `Ctop_tail_pos...`, or `F3_shear...`.
2. Invoke the formal recovery theorem:
   `retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop` or
   `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.
3. Rewrite the staged component to the formal component and apply the recovery
   theorem.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  Full
`DLNFibre` build passed.  `scripts/sorries` reported zero forbidden markers,
and `git diff --check` passed.  Axiom audit for the three theorem names
reported only `[propext, Classical.choice, Quot.sound]`.

Independent xhigh review found no implementation fidelity issue; it required
only that this statement card expose the determinant-chart hypothesis used by
the Lean theorems.

## Nonclaims

This does not prove a closed finite-sum formula for `dTail`, source-stage the
remaining F3 early-tail derivatives, construct a target-side determinant-one
linear equivalence, identify actual and formal determinants, prove measure
transport, normal crossings, pole order, or RLCT.
