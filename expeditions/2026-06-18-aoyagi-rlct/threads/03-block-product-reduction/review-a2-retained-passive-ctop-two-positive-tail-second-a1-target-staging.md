# Review - A2 retained-passive Ctop two-positive-tail second A1 target staging

Date: 2026-06-27.

Reviewer: xhigh `Schrodinger the 2nd`.

Verdict: PASS.

## Scope

Reviewed the reproduction, statement card, and Lean implementation for:

```text
Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

## Findings

No blockers found.

The Lean theorem enforces the two-positive-tail case by using tail length
`(M+1)+1`.  It defines `q0`, `q1`, `p0`, and `p1` as in the reproduction,
starts `Psucc` at `p0.succ`, starts `Psucc1` at `p1.succ`, and target-stages
the second passive tangent using `Dzv.1 q1`.  It does not use the separate
`castSucc` source tangent pattern from the `F3` successor `dEarly` recursion.

The noncommutative matrix order is preserved:

```text
Tail^-1 *
  (((dPsucc1 * A1seed p1 + Psucc1 * targetA1 q1) * A1seed p0)
    + Psucc * targetA1 q0)
  * Tail^-1 * coord.Ctop.
```

The recovery theorem uses the same staged expression and then applies the
formal raw-order `Ctop` recovery.  The reproduction and statement card do not
use quiver-paper evidence and do not claim full staging, determinant/measure
transport, normal crossings, pole order, or RLCT.

## Verification

Controller ran:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
scripts/sorries
git diff --check
env LAKE_SHARED="$PWD/.lake-local-shared" lake env lean /tmp/aoyagi_ctop_axiom_audit.lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

The focused build and full build passed.  `scripts/sorries` reported zero
forbidden markers.  `git diff --check` was clean.  Both new theorems have axiom
footprint `[propext, Classical.choice, Quot.sound]`.
