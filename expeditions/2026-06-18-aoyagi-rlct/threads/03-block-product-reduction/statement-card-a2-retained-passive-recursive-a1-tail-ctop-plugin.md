# Statement Card - A2 retained-passive recursive A1-tail Ctop plug-in

Status: Lean proved; focused/full builds passed; sorry, whitespace, marker,
and axiom audits passed; xhigh independent review passed.

## Claim

For a retained-passive tuple `z` in the determinant chart, the passive
top-left seed-product suffix derivative can be expressed by a target-only
decreasing recursion.  On an actual raw-order derivative target

```text
Dzv = d(topologyTupleEdgeRawOrder)_z(v),
```

the recursion agrees with the actual Frechet derivative of every passive
top-left suffix.

The first value of that recursion can then be used as the `dTail` term in the
first top-left `Ctop` branch:

```text
Dzv.Ctop
  - XsuccF2(0) * coord.solvedA3(0)
  - coord.F2(1) * rawEdgeTupleA3(Dzv, 0)
  + Tail^-1 * dTail * Tail^-1 * coord.Ctop
= formal.Ctop.
```

Multiplication by `Tail` recovers the source `Ctop` tangent.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean names:

```text
retainedPassiveTargetStagedA1passiveTangentAt
retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source
retainedPassiveA1TailTargetStagedFDerivAt
retainedPassiveA1TailTargetStagedFDerivAt_self
retainedPassiveA1TailTargetStagedFDerivAt_step
retainedPassiveA1TailTargetStagedFDerivAt_zero
retainedPassiveA1seedTailProductAt
fderiv_retainedPassive_A1seed_residualFactorProduct_targetStaged_apply
fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

## Assumed

The actual derivative and `Ctop` bridge theorems assume

```text
z in topologyTupleDetChartSet.
```

The target-only recursive definitions themselves only use the retained-passive
coordinate data at `z` and a target tuple `w`.

## Dependencies

- `A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive`;
- `fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply`;
- `Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2`;
- `retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop`.

## Cited

None.

## Deferred

Whole-tuple target-side normalizer; determinant-one proof for that normalizer;
actual derivative determinant equality via the conditional socket;
source-prior transport; inverse-density pushforward; normal crossings; pole
order; RLCT.

## Verification

Controller verification ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
scripts/sorries
git diff --check
rg -n "sorry|axiom|native_decide|#exit" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
#print axioms for the four public theorem names
```

The builds passed.  `scripts/sorries` reported
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`; `git diff --check` was clean;
the forbidden-marker search was clean; the axiom audit for the two derivative
bridges and two `Ctop` theorems reported only
`[propext, Classical.choice, Quot.sound]`.

Independent xhigh review passed in
`review-a2-retained-passive-recursive-a1-tail-ctop-plugin.md`.

## Kill Conditions

- The passive recurrence index must be `m <= M`; at a step,
  `q : Fin M := <m, m<M>` and `p : Fin (M+1) := q.succ`.
- The recurrence order must remain
  `D_{m+1} * data.A1seed(p) + P_{m+1}(z) * targetA1(q)`.
- The `Ctop` target expression must use the endpoint raw edge index
  `0 : Fin (M+1)`, not a passive `q : Fin M`.
- The correction order must remain
  `Tail^-1 * dTail * Tail^-1 * coord.Ctop`.
- The theorem must not claim determinant equality, determinant-one target
  shear, measure transport, normal crossings, pole order, or RLCT.
