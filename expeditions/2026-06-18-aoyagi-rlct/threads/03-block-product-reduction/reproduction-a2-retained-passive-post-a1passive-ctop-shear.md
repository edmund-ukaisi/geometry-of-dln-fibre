# A2 retained-passive post-`A1passive` `Ctop` shear: reproduction

## Scope

This note treats the next target-side normalisation stage after the composed
edge-pair and post-edge-pair `A1passive` stages.  Write

```text
T12 =
  retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt hz,
Dzv = (fderiv raw z) v,
u = T12(Dzv).
```

The existing component bridge proves that `u` already agrees with the formal
raw-order Jacobian in the `A1passive`, `(F2,C)`, and `A3passive` components.
The `Ctop` component is still unnormalised.

## Target Coordinate, Not Source Recovery

The existing target-staged first top-left branch gives

```text
Dzv.Ctop
  - Xsucc(0) * coord.solvedA3(0)
  - coord.F2(0.succ) * rawA3(Dzv,0)
  + Tail^{-1} * dTail * Tail^{-1} * coord.Ctop
  =
formal.Ctop.
```

The companion recovery statement multiplies this parenthesised target
coordinate by `Tail` and recovers the source `Ctop` tangent.  The determinant
one target shear must use the parenthesised coordinate itself.  It must not
replace the coordinate by `Tail * (...)`, since multiplication by the fixed
matrix `Tail` is not a unit-Jacobian shear in the raw tuple coordinates.

## Post-`A1passive` Tail Derivative

For a post-`A1passive` tuple `u`, define the passive-tail derivative by reading
the already staged passive `A1` field directly:

```text
D_M(u) = 0,

D_m(u) =
  D_{m+1}(u) * data.A1seed(q.succ)
    + Psucc(q) * u.A1passive(q),
```

where `q : Fin M` has value `m`, `q.succ : Fin (M+1)`, and `Psucc(q)` is the
fixed seed suffix beginning at `(q.succ).succ`.

This recursion is linear in `u` and uses only `u.A1passive`; it does not read
`u.Ctop`.  On actual derivative targets after `T12`, the existing
`A1passive` bridge gives

```text
u.A1passive(q)
  =
retainedPassiveTargetStagedA1passiveTangentAt z Dzv q.
```

Therefore induction on the same decreasing recursion gives

```text
D_m(u)
  =
retainedPassiveA1TailTargetStagedFDerivAt z Dzv m.
```

In particular, `D_0(u)` is the `dTail` appearing in the existing `Ctop`
target-staged theorem.

## The Shear

For an arbitrary post-`A1passive` tuple `u`, read the source edge-pair from the
already normalised `(F2,C)` fields:

```text
sourcePair(u) =
  (retainedPassiveFormalRawF2CLinearEquivAt hz).symm (u.F2,u.C),

Xsucc(u) =
  retainedPassiveF2SuccessorFamilyLinearMap(sourcePair(u).1).
```

Do not apply the pre-edge-pair target recovery recurrence to `u`.

The next target-side shear fixes every field except `Ctop` and sets

```text
Ctop' =
  u.Ctop
    - Xsucc(u)(0) * coord.solvedA3(0)
    - coord.F2(0.succ) * rawA3(u,0)
    + Tail^{-1} * D_0(u) * Tail^{-1} * coord.Ctop.
```

The correction term is linear in the rest fields

```text
(A1passive,F2,A3passive,C,F3)
```

and independent of the input `Ctop`.  After regrouping the raw tuple as

```text
Ctop x (A1passive,F2,A3passive,C,F3),
```

the map is the upper shear

```text
(Ctop, rest) |-> (Ctop + L(rest), rest).
```

Thus its determinant and absolute determinant are one.

## Actual-Derivative Bridge

For `u = T12(Dzv)`, the already proved facts give:

```text
u.Ctop = Dzv.Ctop,
rawA3(u,0) = rawA3(Dzv,0),
Xsucc(u) = retainedPassiveTargetRecoveredSuccessorF2At z Dzv,
D_0(u) = retainedPassiveA1TailTargetStagedFDerivAt z Dzv 0.
```

Substituting these identities into the shear formula gives exactly the left
side of

```text
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt.
```

Hence the composed target-side normaliser through the `Ctop` stage agrees with
the formal raw-order Jacobian in the `Ctop` component.

## Nonclaims

This is still not the full target normaliser: the `F3` component remains open.
It does not prove full raw-tuple equality, does not feed the conditional
Frechet determinant bridge, and does not prove actual raw-order Frechet
determinant equality, source measure transport, normal crossings, pole order,
or RLCT.
