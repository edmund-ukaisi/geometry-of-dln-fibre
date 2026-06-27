# Reproduction - A2 retained-passive recursive target-staged lower-left tail

Date: 2026-06-27.

Status: controller pen-and-paper reproduction and Lean API design; one-step
core, recursive expression API, actual Frechet-derivative equality bridge, and
recursive positive-tail `F3` plug-in proved in Lean.

This note is independent of the quiver-based paper.  It records the recurrence
that should replace the finite positive-tail `F3` unrolls by a recursive
target-staged derivative of the retained-passive lower-left product tail.

## Setup

Let the retained-passive lower-left tail have positive length `L`.  The ambient
vertex type is `Fin (L+2)`, the solved top factors are indexed by `Fin (L+1)`,
and the active earlier lower-left coordinates are indexed by `Fin L`.

For a current active index `q : Fin L`, set

```text
p = q.castSucc : Fin (L+1),
r = q.succ     : Fin (L+1).
```

The lower-left tail function at `p` is

```text
Tail_q(y) =
  retainedPassiveLowerLeftProductTailSum
    A1_y A3_y C_y p.val (Nat.le_of_lt p.isLt).
```

Write

```text
Cprod(y) = product of C_y from r.castSucc to last,
Cnext(y) = product of C_y from r.succ     to last,
A3p(y)   = A3_y p,
Pcast(y) = product of solvedA1_y from p.castSucc to last,
Psucc(y) = product of solvedA1_y from p.succ     to last,
Next(y)  = lower-left tail at p.val+1.
```

The source tangent attached to the current lower-left free block is

```text
dG = v.A3free(q).
```

In Lean's tuple projection notation this is `v.2.2.1 q`.  It is distinct from
the `C`-block tangent `v.2.2.2.1 r`.

## One-step derivative recurrence

The already-proved product-rule recurrence gives

```text
d Tail_q =
  -(((d Cnext) * C_r + Cnext * dC_r) * A3p * Pcast^-1)
  - (Cprod * dG * Pcast^-1)
  + Cprod * A3p * Pcast^-1
      * (dPsucc * solvedA1(p) + Psucc * dAcur)
      * Pcast^-1
  + dNext.
```

Here

```text
dPsucc = d(Psucc)_z(v),
dNext  = d(Next)_z(v),
dAcur  = d(solvedA1(p))_z(v).
```

The first reusable Lean helper should package exactly this RHS while leaving
`dAcur`, `dPsucc`, and `dNext` explicit.  This avoids mixing the lower-left
tail recurrence with the separate solved-`A1` derivative split.

## Solved-A1 current tangent

For the first active index, `L = M+1` and

```text
q = 0 : Fin (M+1).
```

The current solved-`A1` tangent is the zero branch:

```text
dAcur =
  Tail^-1 * v.Ctop
    - Tail^-1 * dTail * Tail^-1 * coord.Ctop.
```

In Lean this is the tangent of `solvedA1(0)` proved by

```text
fderiv_retainedPassive_toCoordinateData_solvedA1_zero_apply
```

and already consumed by

```text
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply.
```

For a successor active index, with `s : Fin M`,

```text
q = s.succ     : Fin (M+1),
u = s.castSucc : Fin (M+1),
p = q.castSucc : Fin ((M+1)+1).
```

The current solved-`A1` tangent is

```text
dAcur = v.A1passive(u).
```

In Lean tuple notation this is `v.1 u`, not `v.1 q`.  The proof uses
`u.succ = p`, i.e. `Fin.succ_castSucc s`.

## Terminal base

The recursive target-staged derivative object should stop at the zeroed-final
tail.  The base is at `m = L`, not `m = L+1`:

```text
D_L = 0.
```

The existing Lean theorem is

```text
fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply.
```

This is a derivative statement about the zeroed-final tail.  It is not the
terminal solved lower-left block and it does not erase the whole final
product-rule boundary.  At the final active index, the derivative of `Cnext`
is zero because `Cnext` is the empty product, but the term

```text
Cnext * dC_r
```

still remains.

## Positive-tail F3 plug-in

For positive tail length `L`, the eventual target-staged `F3` bridge should use
the recursive derivative value at the first active index:

```text
dEarly = D_0.
```

Then the positive-tail `F3` equation has the same outer shape as the existing
finite theorems:

```text
Dzv.F3
  - dEarly * coord.solvedA1(last L)
  + (coord.F3 - Early(z)) * terminalTargetA1
  = formal.F3.
```

The terminal factor is the already target-staged last solved-`A1` tangent:

```text
terminalTargetA1 =
  Dzv.A1(qLast)
    - XsuccF2(qLast.succ) * coord.solvedA3(qLast.succ)
    - coord.F2(qLast.succ.succ) * rawA3(Dzv, qLast.succ),
```

with `qLast : Fin L` the final active lower-left index.  The zero-tail case
`L=0` has no such `qLast` and remains handled by the existing zero-tail `F3`
theorem.

## First Lean rung

The first Lean target is deliberately smaller than the full recursive object:

```text
retainedPassiveLowerLeftTailStepCoreAt
```

It packages the one-step RHS of the recurrence with parameters

```text
dAcur, dPsucc, dNext.
```

The immediate theorem should restate the generic already-proved recurrence
through this helper.  After that compiles, the zero and successor specialized
theorems can be restated through the same helper.  Only then should we build a
Nat-recursive target-staged derivative object.

The one-step helper and the Nat-recursive expression API have now landed.  The
recursive API is:

```text
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_zero
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_succ
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_self
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_step
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_zero
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_succ
```

The bridge proving that this recursive expression equals the actual Frechet
derivative of the zeroed-final lower-left product tail under the
determinant-chart hypothesis has now landed:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
```

The proof is the same recurrence as above, formalised by decreasing induction
on the tail index.  The base is the zeroed-final tail `m = M+1`; the step uses
the zero or successor one-step core theorem and substitutes the induction
hypothesis only into the `dNext` argument.  The actual product-tail side is
typed with the widened proof `m <= M+2`, while the staged target expression
keeps the intended index `m <= M+1`.

The staged derivative value at `m=0` is now used as the `dEarly` term in the
positive-tail `F3` bridge by:

```text
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

The proof starts from the terminal-target-staged positive-tail `F3` theorem at
`qLast : Fin (M+1) := Fin.last M`, where `qLast.succ = Fin.last (M+1)` by
definition.  It then rewrites the actual early-tail derivative
`(fderiv Earlyfun z) v` using
`fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply` with
`(M := M)` and `m = 0`.  The resulting `F3` recovery theorem uses the same
staged expression and the existing formal raw-order recovery lemma, with right
multiplication by `(-(coord.solvedA1 (Fin.last (M+1))))^-1`.

## Kill conditions

- Do not use `v.1 q` in the successor branch.  The tangent is `v.1 u` with
  `u = s.castSucc`.
- Do not replace the zero branch by a passive source tangent.
- Do not identify `dG = v.2.2.1 q` with the `C` tangent `v.2.2.2.1 r`.
- Do not choose the recursive base at `m = L+1`; the useful base is the
  zeroed-final tail at `m = L`.
- Do not assume `Psucc = 1` or `dPsucc = 0`.
- Do not erase `Cnext * dC_r` at the terminal active index.
- Do not commute or distribute noncommutative matrix factors.
- Do not claim determinant equality or a target-side linear equivalence from
  this helper alone.

## Nonclaims

This note and the landed Lean theorems do not construct the determinant-one
target normalizer.  They do not prove determinant equality, source-prior
transport, inverse-density pushforward, normal crossings, pole order, or RLCT.
