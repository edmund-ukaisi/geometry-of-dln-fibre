# Reproduction - A2 retained-passive recursive target-staged A1 tail

Date: 2026-06-27.

Status: controller pen-and-paper reproduction and Lean target design; the
recursive target-staged passive top-left tail derivative, actual derivative
bridge, and `Ctop` plug-in are proved in Lean.

This note is independent of the quiver-based paper.  It records the elementary
product-rule recurrence for the passive top-left suffix appearing in Aoyagi's
p. 13 retained-passive coordinate algebra.

## Setup

For a retained-passive tuple with parameter `M`, the passive top-left source
coordinates are indexed by `Fin M`.  If

```text
q : Fin M,
```

then the corresponding solved seed index is

```text
p = q.succ : Fin (M+1).
```

For `m <= M`, define the seed-product suffix

```text
P_m(y) =
  residualFactorProduct
    (ofTopologyTuple y).A1seed
    (Fin.last (M+1))
    <m+1>.
```

Thus `P_0` is `retainedPassiveA1TailAfterFirst`, and `P_M` is the empty suffix
at `Fin.last (M+1)`, hence `P_M = 1`.

Let

```text
w : RetainedPassiveRawTopologyTuple
```

be a target tangent.  The target-only passive `A1` tangent at `q` is

```text
alpha_q(w) =
  w.A1passive(q)
  - XsuccF2(q.succ) * coord.solvedA3(q.succ)
  - coord.F2(q.succ.succ) * rawEdgeTupleA3(w, q.succ),
```

where `XsuccF2 = retainedPassiveTargetRecoveredSuccessorF2At z w`.

When `w = d(topologyTupleEdgeRawOrder)_z(v)`, the already-proved passive `A1`
target-staging theorem gives

```text
alpha_q(w) = v.A1passive(q).
```

## Recursive derivative

Define `D_m#(w)` by decreasing recursion on `m <= M`:

```text
D_M#(w) = 0,
```

and for `m < M`, with

```text
q = <m, m < M> : Fin M,
p = q.succ    : Fin (M+1),
```

set

```text
D_m#(w) =
  D_{m+1}#(w) * data.A1seed(p)
  + P_{m+1}(z) * alpha_q(w).
```

The order is forced by the product decomposition

```text
P_m = P_{m+1} * data.A1seed(p).
```

No commutation is used.

## Actual derivative check

For an actual raw-order derivative target

```text
w = d(topologyTupleEdgeRawOrder)_z(v),
```

the ordinary product rule gives

```text
d(P_m)_z(v) =
  d(P_{m+1})_z(v) * data.A1seed(p)
  + P_{m+1}(z) * d(A1seed(p))_z(v).
```

The passive target-staging theorem replaces the last factor by
`alpha_q(w)`.  Downward induction from the base `d(P_M)=d(1)=0` therefore
proves

```text
d(P_m)_z(v) = D_m#(w)
```

for every `m <= M`.  The full passive top-left tail after the first edge is
the `m=0` case.

## Ctop plug-in

The existing source-staged first top-left branch has the shape

```text
Dzv.Ctop
  - sourceF2(0) * coord.solvedA3(0)
  - coord.F2(1) * sourceA3(0)
  + Tail^-1 * dTailActual * Tail^-1 * coord.Ctop
= formal.Ctop.
```

The plus sign comes from substituting

```text
d(Tail^-1) = - Tail^-1 * dTailActual * Tail^-1
```

into a source formula containing `- d(Tail^-1) * coord.Ctop`.

Now replace:

```text
sourceF2      by retainedPassiveTargetRecoveredSuccessorF2At z Dzv,
sourceA3(0)   by rawEdgeTupleA3(Dzv, 0) under left multiplication by coord.F2(1),
dTailActual   by D_0#(Dzv).
```

The target-staged branch is therefore

```text
Dzv.Ctop
  - XsuccF2(0) * coord.solvedA3(0)
  - coord.F2(1) * rawEdgeTupleA3(Dzv, 0)
  + Tail^-1 * D_0#(Dzv) * Tail^-1 * coord.Ctop
= formal.Ctop.
```

Multiplying the same formal component by `Tail` and using the existing formal
raw-order recovery theorem gives the source `Ctop` tangent.

## Lean route

The Lean implementation follows this calculation with:

```text
retainedPassiveTargetStagedA1passiveTangentAt
retainedPassiveA1TailTargetStagedFDerivAt
retainedPassiveA1seedTailProductAt
```

and proves:

```text
fderiv_retainedPassive_A1seed_residualFactorProduct_targetStaged_apply
fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

## Nonclaims

This calculation does not construct the whole target-side linear equivalence,
does not prove determinant one, determinant equality, source-prior transport,
inverse-density pushforward, normal crossings, pole order, or RLCT.
