# Reproduction - A2 retained-passive F3 positive-tail dEarly substitution

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; xhigh review
passed.

This note is independent of the quiver-based paper.  It records the next
positive-tail terminal `F3` consumer after the terminal `dLast` factor has
already been target-staged.

## Setup

Work one positive tail step by writing the raw tuple length as `M+1`.  Thus
the source tuple has vertex type `Fin ((M+1)+2)`, solved top factors indexed
by `Fin ((M+1)+1)`, and the earlier lower-left tail starts at the first
nonterminal index.

Set

```text
q0 = 0          : Fin (M+1),
p0 = q0.castSucc : Fin ((M+1)+1),
r0 = q0.succ     : Fin ((M+1)+1),
qLast = Fin.last M : Fin (M+1).
```

The existing positive-tail `F3` theorem with `qLast.succ = Fin.last (M+1)`
gives

```text
Dzv.F3
  - dEarly * coord.solvedA1(Fin.last (M+1))
  + (coord.F3 - Early(z)) * dLast_target
  = formal.F3,
```

where the already-staged terminal factor is

```text
dLast_target =
  Dzv.A1(qLast)
    - XsuccF2(qLast.succ) * coord.solvedA3(qLast.succ)
    - coord.F2(qLast.succ.succ) * rawA3(Dzv,qLast.succ).
```

The remaining unstaged factor is `dEarly = (fderiv Earlyfun z) v`, where
`Earlyfun` is the lower-left product-tail sum at the first index.

## Calculation

The first index is the zero-current branch of the retained-passive `dEarly`
recurrence.  The landed theorem

```text
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply
```

applies directly with the ambient parameter `M`, because its source type is
`Fin ((M+1)+2)` and its current edge is `q0 = 0 : Fin (M+1)`.

With

```text
Pcast(y) = product solvedA1_y from p0.castSucc,
Psucc(y) = product solvedA1_y from p0.succ,
Tail(y)  = retainedPassiveA1TailAfterFirst(A1seed_y),
dTail    = d(Tail)_z(v),
Next(y)  = Early tail starting at p0.val+1,
```

the first-index formula is

```text
dEarly =
  -(((dCnext) * C_r0 + Cnext * dC_r0) * A3p * Pcast^-1)
  - (Cprod * dG * Pcast^-1)
  + Cprod * A3p * Pcast^-1
      * (dPsucc * solvedA1(p0)
          + Psucc *
              (Tail^-1 * v.Ctop
                - Tail^-1 * dTail * Tail^-1 * coord.Ctop))
      * Pcast^-1
  + dNext.
```

Substituting only this identity into the `F3` bridge gives

```text
Dzv.F3
  - dEarly_expanded * coord.solvedA1(Fin.last (M+1))
  + (coord.F3 - Early(z)) * dLast_target
  = formal.F3.
```

The matrix order is unchanged.  In particular, the expanded `dEarly` is still
right-multiplied as a whole by the terminal solved top factor
`coord.solvedA1(Fin.last (M+1))`.

## Lean Scope

Planned Lean addition in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

It should start from

```text
F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

with `M := M+1`, `q := Fin.last M`, then rewrite `(fderiv Earlyfun z) v` by
the zero-current `dEarly` theorem above.

## Kill Conditions

- Do not use the successor-current `dEarly` theorem for the first index.
- Do not change the terminal `dLast` target-staged term.
- Do not distribute the outer `- dEarly * coord.solvedA1(Fin.last (M+1))`.
- Do not expand `dPsucc`, `dTail`, `dCnext`, or the successor `Nextfun`
  derivative.
- Do not terminal-clean the positive-tail theorem or treat `Psucc` as empty.
- Do not claim whole-tuple target staging, determinant equality, measure
  transport, normal crossings, pole order, or RLCT.

## Nonclaims

This is a single consumer substitution for the first earlier-tail derivative
inside the positive-tail `F3` bridge.  It is not a closed formula for the full
earlier lower-left tail derivative and not a final target-side linear
equivalence.
