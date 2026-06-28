# A2 retained-passive post-edge-pair `A1passive` raw-tuple shear: reproduction

## Scope

This note reproduces the next target-side normalisation after the raw-tuple
edge-pair shear.  The input tuple is understood to have already passed through
the target edge-pair map

```text
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt.
```

Thus its `(F2,C)` fields are the target-normalised fields.  We now change only
the passive `A1` field in the raw tuple

```text
w = (A1passive, F2, A3passive, C, Ctop, F3).
```

The calculation is finite-dimensional linear algebra.  It is not the full
target normaliser, not the actual Frechet determinant equality, and not a
measure-transport theorem.

## Source Pair Read From Post-Edge-Pair Coordinates

Fix a retained-passive base point `z` in the determinant chart and write
`coord = ofTopologyTuple(z).toCoordinateData`.  For a post-edge-pair tuple
`w`, define

```text
(X,Y) =
  (retainedPassiveFormalRawF2CLinearEquivAt hz).symm (w.F2,w.C).
```

The successor family is

```text
Xsucc_last = 0,
Xsucc_{p.castSucc} = cast (X_{p.succ}).
```

This is the important post-edge-pair choice.  We do not define the `A1`
normalisation by `retainedPassiveTargetRecoveredSuccessorF2At z w`, because
that recurrence reads `rawEdgeTupleA1 w`.  After `(F2,C)` has already been
normalised, the clean triangular object is the formal inverse of the
normalised `(F2,C)` pair.

When `w` is the edge-pair shear of an actual raw-order derivative target, the
previously proved identity

```text
retainedPassiveFormalRawF2CLinearEquivAt_symm_targetEdgePairShearAt_fst
```

identifies this `X` with the target-recovered source `F2` family of the
pre-edge-pair derivative tuple.

## Forward Shear

For `p : Fin M`, define

```text
A1passive'_p =
  A1passive_p
    - Xsucc_{p.succ} * coord.solvedA3_{p.succ}
    - coord.F2_{p.succ.succ} * rawEdgeTupleA3(w)_{p.succ}.
```

All other fields are fixed:

```text
F2' = F2,  A3passive' = A3passive,  C' = C,  Ctop' = Ctop,  F3' = F3.
```

This is linear in the post-edge-pair tuple.  The `Xsucc` term is linear in
`(F2,C)` because the formal `(F2,C)` inverse is linear.  The lower-left readout
`rawEdgeTupleA3(w)_{p.succ}` is linear in `(A3passive,F3)`.

## Inverse and Determinant

The inverse fixes the same non-`A1passive` fields and adds back the same
linear correction:

```text
A1passive_p =
  A1passive'_p
    + Xsucc_{p.succ} * coord.solvedA3_{p.succ}
    + coord.F2_{p.succ.succ} * rawEdgeTupleA3(w')_{p.succ}.
```

Because the rest fields are fixed, the correction is computed from the same
`(F2,C,A3passive,F3)` data in the forward and inverse directions.  In product
form this is the upper shear

```text
(A1passive, rest) |-> (A1passive - L(rest), rest).
```

Its inverse is `(A1passive, rest) |-> (A1passive + L(rest), rest)`, and its
determinant is `1`.  The absolute determinant is therefore also `1`.

## Actual-Derivative Bridge

Let `Dzv = (fderiv raw z) v` and let `E` be the already-landed raw-tuple
edge-pair shear.  The post-edge-pair `A1` shear `S` satisfies

```text
(S (E Dzv)).A1passive = (retainedPassiveFormalRawOrderJacobianAt z v).A1passive.
```

The proof rewrites:

1. `E` fixes `A1passive` and `rawEdgeTupleA3`;
2. the formal inverse of the normalised `(F2,C)` pair recovers the old
   target-recovered `F2`;
3. the existing target-staged theorem
   `A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
   supplies the final equality.

Since `S` fixes the `(F2,C)` fields, the previous edge-pair bridge also gives
the `F2` and `C` components of `S (E Dzv)` as the formal raw-order components.
No claim is made for `A3passive`, `Ctop`, or `F3` at this stage.
