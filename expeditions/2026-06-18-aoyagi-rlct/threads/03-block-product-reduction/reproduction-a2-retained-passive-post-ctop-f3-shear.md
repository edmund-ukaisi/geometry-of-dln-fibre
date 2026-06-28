# A2 retained-passive post-`Ctop` `F3` shear: reproduction

## Scope

This note treats the final target-side component after the already landed
edge-pair, post-edge-pair `A1passive`, and post-`A1passive` `Ctop` stages.
Write

```text
T123 =
  retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt hz,
Dzv = (fderiv raw z) v,
u = T123(Dzv).
```

The raw tuple order is

```text
(A1passive, F2, A3passive, C, Ctop, F3).
```

The first five fields of `u` are now the target-staged coordinates already
matched against the formal raw-order Jacobian.  The remaining coordinate is
`F3`.

## Zero Passive Tail

When `M = 0`, the existing target-staged theorem gives

```text
Dzv.F3
  + coord.F3 *
      (Dzv.Ctop
        - Xsucc(0) * coord.solvedA3(0)
        - coord.F2(0.succ) * rawA3(Dzv,0))
  =
formal.F3.
```

The landed `Ctop` shear sends

```text
u.Ctop =
  Dzv.Ctop
    - Xsucc(0) * coord.solvedA3(0)
    - coord.F2(0.succ) * rawA3(Dzv,0).
```

The previous stages leave `F3` unchanged.  Hence the final target coordinate is

```text
F3' = u.F3 + coord.F3 * u.Ctop.
```

This is linear in the non-`F3` fields and independent of `u.F3` except for the
identity term.

## Positive Passive Tail

For positive passive-tail length, write the raw length as `M + 1`.  Let

```text
qLast : Fin (M + 1) := Fin.last M,
LastTop := coord.solvedA1 (Fin.last (M + 1)),
Early := Earlyfun z.
```

The existing target-only `F3` theorem gives

```text
Dzv.F3
  - dEarly(Dzv) * LastTop
  + (coord.F3 - Early) *
      (Dzv.A1passive(qLast)
        - Xsucc(qLast.succ) * coord.solvedA3(qLast.succ)
        - coord.F2(qLast.succ.succ) * rawA3(Dzv,qLast.succ))
  =
formal.F3.
```

The `A1passive` stage sends the terminal parenthesised term to
`u.A1passive(qLast)`, and the later `Ctop` stage leaves `A1passive` unchanged.
Thus the intended post-`Ctop` formula is

```text
F3' =
  u.F3
    - dEarly_postC(u) * LastTop
    + (coord.F3 - Early) * u.A1passive(qLast).
```

The only nontrivial new object is `dEarly_postC`.  It is the lower-left
early-tail derivative rewritten in the already normalised coordinates

```text
(u.A1passive, u.F2, u.A3passive, u.C, u.Ctop).
```

It must not re-run the pre-edge-pair target recovery recurrences on
`(u.F2,u.C)`, and it must not use the source-recovery `Ctop` coordinate.

## Post-`Ctop` Current Solved `A1`

In the lower-left recurrence, the current solved `A1` tangent at index zero is
the only place where `Ctop` enters.  Before the `Ctop` stage the target-only
helper computes

```text
Tail^{-1} * recoveredSourceCtop - Tail^{-1} * dTail * Tail^{-1} * coord.Ctop.
```

The recovered source `Ctop` is `Tail` times the target `Ctop` coordinate.  After
the `Ctop` stage the target coordinate is already stored as `u.Ctop`, so the
post-`Ctop` zero-index current solved `A1` tangent is

```text
u.Ctop - Tail^{-1} * dTail_postA1(u) * Tail^{-1} * coord.Ctop.
```

For successor indices it is simply the already staged passive field:

```text
currentSolvedA1(m + 1) = u.A1passive(m).
```

Here `dTail_postA1` is the linear passive-tail derivative from the `Ctop`
stage.  On `u = T123(Dzv)`, it agrees with
`retainedPassiveA1TailTargetStagedFDerivAt z Dzv 0`.

## Post-Edge Source `C` Readout

The positive-tail lower-left recurrence also needs the source stored-`C`
tangent at each edge.  In post-edge-pair coordinates this must be read from
the formal inverse of the already normalised edge pair:

```text
sourcePair(u) =
  (retainedPassiveFormalRawF2CLinearEquivAt hz).symm (u.F2,u.C),

sourceC(u,q) = sourcePair(u).2(q).
```

This replaces `retainedPassiveTargetRecoveredSourceCAt z u q`, which is a
pre-edge-pair recovery and would normalise the pair a second time.

## Determinant Shape

The final shear fixes every field except `F3`.  In raw order it is a lower
unitriangular block map

```text
(rest,F3) |-> (rest, F3 + L(rest)).
```

Equivalently, regroup the raw tuple as

```text
F3 x (A1passive,F2,A3passive,C,Ctop)
```

and use the existing upper-shear determinant lemma.  The correction `L` is:

```text
M = 0:
  L(rest) = coord.F3 * rest.Ctop.

M = M' + 1:
  L(rest) =
    - dEarly_postC(rest) * LastTop
    + (coord.F3 - Early) * rest.A1passive(qLast).
```

In both cases `L` is linear in the rest fields, so the determinant and absolute
determinant are one.

## Actual-Derivative Bridge

For `u = T123(Dzv)`:

```text
u.F3 = Dzv.F3,
u.Ctop = target-staged Ctop coordinate,
u.A1passive(qLast) = target-staged terminal A1passive coordinate,
dEarly_postC(u) = retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt hz Dzv 0.
```

Substituting these identities into the post-`Ctop` `F3` shear gives exactly the
left side of the existing `F3` target-staged theorem:

```text
F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

in the zero-tail case, and

```text
F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

in the positive-tail case.

## Implementation Boundary

The zero-tail shear is implementation-ready: it needs only the `F3` focus
regrouping and the linear map `Ctop |-> coord.F3 * Ctop`.

The positive-tail shear additionally needs a post-`Ctop` linear-map package for
`dEarly_postC`, including post-edge source-`C` readout and post-`Ctop`
zero-index solved-`A1` readout.  Feeding the existing
`retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt` directly with `u` is
not sound, because that helper expects pre-edge-pair target data.

## Nonclaims

This stage is only target-side raw-tuple normalisation.  It does not prove
source `F3` recovery, does not right-multiply by `(-LastTop)^{-1}`, does not
prove actual Frechet determinant equality, does not prove source measure
transport, and does not prove normal crossings, pole order, or RLCT.
