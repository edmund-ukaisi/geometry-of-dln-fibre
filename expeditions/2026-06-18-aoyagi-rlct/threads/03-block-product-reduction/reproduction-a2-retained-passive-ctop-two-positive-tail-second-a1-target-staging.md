# Reproduction - A2 retained-passive Ctop two-positive-tail second A1 target staging

Date: 2026-06-27.

Status: reproduced; Lean equality theorem and recovery companion proved; xhigh
independent review passed.

This note is independent of the quiver-based paper.  It records one further
elementary target-staging step in the retained-passive `Ctop` bridge: after the
first passive `A1` tangent has already been target-staged, recurse once into the
remaining top-left suffix derivative and target-stage the next passive `A1`
tangent.

## Setup

Work at passive tail length `(M+1)+1`, so there are at least two passive
top-left source coordinates.  Let

```text
raw = topologyTupleEdgeRawOrder,
data = ofTopologyTuple z,
coord = data.toCoordinateData,
Dzv = (fderiv raw z) v,
Tail = retainedPassiveA1TailAfterFirst(data.A1seed).
```

Use the first two passive source indices

```text
q0 = 0                 : Fin ((M+1)+1),
q1 = (0 : Fin (M+1)).succ : Fin ((M+1)+1),
```

and their corresponding seed-factor indices

```text
p0 = q0.succ : Fin (((M+1)+1)+1),
p1 = q1.succ : Fin (((M+1)+1)+1).
```

The already-landed first-passive `Ctop` formula contains the suffix derivative

```text
(fderiv Psucc z) v
```

where

```text
Psucc(y) =
  residualFactorProduct
    (A1seed(y)) (Fin.last (((M+1)+1)+1)) p0.succ.
```

Since `p0.succ = p1.castSucc`, this is exactly the derivative of the
residual product whose first current factor is `data.A1seed p1`.

## Second Passive Product Rule

Apply the generic retained-passive passive-`A1` suffix derivative theorem at

```text
q = q1 : Fin ((M+1)+1),
p = q1.succ = p1.
```

The next residual suffix is

```text
Psucc1(y) =
  residualFactorProduct
    (A1seed(y)) (Fin.last (((M+1)+1)+1)) p1.succ.
```

The product rule gives

```text
(fderiv Psucc z) v =
  (fderiv Psucc1 z) v * data.A1seed p1
  + Psucc1(z) * v.A1passive(q1).
```

Here the tangent is `v.A1passive(q1)`.  This differs from the successor
`dEarly` recursion pattern, where the helper theorem introduces a separate
`castSucc` source tangent.  For this passive seed-product derivative the
current factor `data.A1seed p1` corresponds directly to the passive source
coordinate `q1`.

The target-staged passive `A1` recovery rewrites this tangent as

```text
targetA1(q1) =
  Dzv.A1passive(q1)
  - XsuccF2(q1.succ) * coord.solvedA3(q1.succ)
  - coord.F2(q1.succ.succ) * rawEdgeTupleA3(Dzv, q1.succ),
```

where

```text
XsuccF2 = retainedPassiveTargetRecoveredSuccessorF2At(z, Dzv).
```

Thus the second-stage suffix derivative is

```text
(fderiv Psucc z) v =
  (fderiv Psucc1 z) v * data.A1seed p1
  + Psucc1(z) * targetA1(q1).
```

The next derivative `(fderiv Psucc1 z) v` remains explicit.

## Ctop Substitution

The existing first-passive target-staged `Ctop` bridge is

```text
Dzv.Ctop
  - XsuccF2(0) * coord.solvedA3(0)
  - coord.F2((0 : Fin (((M+1)+1)+1)).succ)
      * rawEdgeTupleA3(Dzv, 0)
  + Tail^-1 *
      ((fderiv Psucc z) v * data.A1seed p0
        + Psucc(z) * targetA1(q0))
      * Tail^-1 * coord.Ctop
  = formal.Ctop.
```

Substituting only the second-stage product-rule equality yields

```text
Dzv.Ctop
  - XsuccF2(0) * coord.solvedA3(0)
  - coord.F2((0 : Fin (((M+1)+1)+1)).succ)
      * rawEdgeTupleA3(Dzv, 0)
  + Tail^-1 *
      (((fderiv Psucc1 z) v * data.A1seed p1
          + Psucc1(z) * targetA1(q1))
        * data.A1seed p0
        + Psucc(z) * targetA1(q0))
      * Tail^-1 * coord.Ctop
  = formal.Ctop.
```

The matrix order is unchanged: the expanded second-stage derivative is still
left-multiplied by `Tail^-1`, then multiplied on the right by
`data.A1seed p0`, then the outer expression is right-multiplied by
`Tail^-1 * coord.Ctop`.

## Recovery Consumer

The matching source recovery is obtained by multiplying the same staged
left-hand expression by `Tail` on the left and using the formal raw-order
recovery theorem for `Ctop`:

```text
Tail * stagedCtopExpression = v.Ctop.
```

No further expansion is involved in the recovery theorem.

## Boundary Cases

This theorem is only for tail length `(M+1)+1`; the one-positive-tail theorem
is the boundary case already proved.  The theorem does not simplify the
terminal case when `M=0`, where `Psucc1` is the empty suffix and some endpoint
terms may have special forms.  Those cleanups require separate statements.

## Lean Scope

Target file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Planned Lean names:

```text
Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

Both Lean targets are now proved in
`RetainedPassiveCoordinatesJacobian.lean`.  Focused Jacobian build, full
`DLNFibre` build, `scripts/sorries`, `git diff --check`, and axiom audit passed.
The axiom footprint is `[propext, Classical.choice, Quot.sound]`.

Dependencies:

- `Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop`.

## Kill Conditions

- State the theorem only for tail length `(M+1)+1`.
- Use `q1`, not the first source index and not the F3-style `castSucc`
  tangent, for the second passive `A1` tangent.
- Preserve the noncommutative order
  `Tail^-1 * (((...) * data.A1seed p0) + ...) * Tail^-1 * coord.Ctop`.
- Leave `(fderiv Psucc1 z) v` explicit.
- Do not simplify the `M=0` terminal second-stage suffix.
- Do not claim full `Ctop` or `F3` target staging, determinant equality,
  measure transport, normal crossings, pole order, or RLCT.
