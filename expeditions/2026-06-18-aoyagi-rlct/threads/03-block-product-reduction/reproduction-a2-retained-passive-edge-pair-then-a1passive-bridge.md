# A2 retained-passive edge-pair then `A1passive` bridge: reproduction

## Scope

This note composes two already-proved determinant-one target-side shears:

```text
E = retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
S = retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt.
```

The composed map is `T = E.trans S`, so `T(w) = S(E(w))`.  This is only the
first two target-normalisation stages.  It is not the full target normaliser,
because the `Ctop` and `F3` stages remain open.

## Determinant

Both stages have absolute determinant one:

```text
|det E| = 1,
|det S| = 1.
```

For the composition,

```text
det(T) = det(S ∘ E) = det(S) det(E),
```

so `|det T| = 1`.  This determinant statement belongs only to the composed
target-side linear equivalence, not to the actual raw-order Frechet derivative.

## `(F2,C)` Components

Let

```text
Dzv = (fderiv raw z) v.
```

The edge-pair shear sends the `(F2,C)` fields of `Dzv` to

```text
retainedPassiveTargetEdgePairShearAt z Dzv.
```

The post-edge-pair `A1passive` shear fixes all rest fields, including `F2` and
`C`.  Hence the composed `(F2,C)` fields are those of `E(Dzv)`.  The existing
edge-pair bridge gives

```text
retainedPassiveTargetEdgePairShearAt z Dzv
  =
(((retainedPassiveFormalRawOrderJacobianAt z) v).F2,
 ((retainedPassiveFormalRawOrderJacobianAt z) v).C).
```

## `A1passive` Component

For post-edge-pair input `E(Dzv)`, the `A1passive` shear subtracts

```text
Xsucc(p.succ) * coord.solvedA3(p.succ)
  + coord.F2(p.succ.succ) * rawEdgeTupleA3(E(Dzv))(p.succ),
```

where

```text
Xsucc =
  successor (((retainedPassiveFormalRawF2CLinearEquivAt hz).symm
    (E(Dzv).F2,E(Dzv).C)).1).
```

The edge-pair shear fixes raw lower-left readouts:

```text
rawEdgeTupleA3(E(Dzv))(q) = rawEdgeTupleA3(Dzv)(q).
```

The formal inverse of the edge-pair-normalised `(F2,C)` fields recovers the
pre-edge-pair target-recovered source `F2` family:

```text
((retainedPassiveFormalRawF2CLinearEquivAt hz).symm
  (retainedPassiveTargetEdgePairShearAt z Dzv)).1
  =
retainedPassiveTargetRecoveredF2At z Dzv.
```

Taking successors gives the exact `Xsucc` used in the existing
target-staged `A1passive` theorem.  Therefore the composed `A1passive` field
is

```text
Dzv.A1passive p
  - retainedPassiveTargetRecoveredSuccessorF2At z Dzv (p.succ)
      * coord.solvedA3(p.succ)
  - coord.F2(p.succ.succ) * rawEdgeTupleA3(Dzv)(p.succ),
```

which is already proved equal to the formal raw-order `A1passive` field by

```text
A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt.
```

## `A3passive` Component

Both `E` and `S` fix the `A3passive` field.  The actual derivative `A3passive`
component is already identified with the formal raw-order component by

```text
rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt.
```

## Nonclaims

No statement here identifies the `Ctop` or `F3` fields with the formal
raw-order Jacobian.  Consequently this is not a theorem

```text
T ((fderiv raw z) v) = retainedPassiveFormalRawOrderJacobianAt z v.
```

It also does not prove actual raw-order Frechet determinant equality, source
measure transport, normal crossings, pole order, or RLCT.
