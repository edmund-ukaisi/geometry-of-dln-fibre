# Reproduction - A2 retained-passive F3 two-positive-tail next-successor substitution

Date: 2026-06-27.

Status: xhigh pen-and-paper scouts reproduced; Lean proved; focused/full
builds and audits passed; xhigh reviews passed.

This note is independent of the quiver-based paper.  It records the next
consumer step after the positive-tail `F3` theorem whose first `dEarly`
recurrence was substituted.

## Setup

The landed positive-tail theorem writes the tail length as `M+1`.  Its
first-index expansion leaves one recursive derivative explicit:

```text
dNext0 = (fderiv Next0 z) v,
```

where `Next0` is the lower-left product-tail sum starting at `p0.val+1`.
For the first recursive substitution to exist, the positive tail must have at
least two indices.  We therefore write the tail length as `(M+1)+1`.

Set

```text
q0 = 0                    : Fin ((M+1)+1),
p0 = q0.castSucc          : Fin (((M+1)+1)+1),
r0 = q0.succ              : Fin (((M+1)+1)+1),
qLast = Fin.last (M+1)    : Fin ((M+1)+1).
```

The first zero-index `dEarly` theorem gives the same formula as before, but
with terminal factor `coord.solvedA1(Fin.last ((M+1)+1))` and with the
remaining recursive term `dNext0`.

## Successor Reindexing

To expand `dNext0`, instantiate the successor-index `dEarly` theorem with

```text
s0 = 0          : Fin (M+1),
q1 = s0.succ    : Fin ((M+1)+1),
u1 = s0.castSucc: Fin ((M+1)+1),
p1 = q1.castSucc: Fin (((M+1)+1)+1),
r1 = q1.succ    : Fin (((M+1)+1)+1).
```

Then `p1.val = p0.val+1`, so the successor theorem's `Tailfun` is exactly
the old `Next0`.  The solved-`A1` derivative branch uses `u1`, not `q1`,
because

```text
u1.succ = s0.castSucc.succ = s0.succ.castSucc = q1.castSucc = p1
```

by `Fin.succ_castSucc`.  Hence the source tangent in the successor branch is

```text
v.1 u1,
```

not `v.1 q1`.

## Calculation

The successor substitution replaces only the final summand of the already
expanded first `dEarly`:

```text
dNext0 =
  -(((dCnext1) * C_r1 + Cnext1 * dC_r1) * A3p1 * Pcast1^-1)
  - (Cprod1 * dG1 * Pcast1^-1)
  + Cprod1 * A3p1 * Pcast1^-1
      * (dPsucc1 * solvedA1(p1) + Psucc1 * v.1 u1)
      * Pcast1^-1
  + dNext1.
```

Substituting this into the first expanded `dEarly` and then into the terminal
`F3` bridge gives

```text
Dzv.F3
  - dEarly_expanded_once_more * coord.solvedA1(Fin.last ((M+1)+1))
  + (coord.F3 - Early(z)) * dLast_target
  = formal.F3.
```

The terminal `dLast_target` expression is unchanged.  The whole new `dEarly`
expression is still right-multiplied by the terminal solved top-left factor;
no distribution across that outer product is part of this slice.

The recovery companion uses exactly the same staged expression.  Since the
staged expression is the formal raw-order `F3` tangent, the already proved
formal raw-order recovery gives

```text
staged_F3 * (-(coord.solvedA1(Fin.last ((M+1)+1))))^-1
  = source_F3_tangent.
```

This is only a consumer of the equality theorem and
`retainedPassiveFormalRawOrderJacobianAt_recovers_F3`; it performs no further
expansion of `dEarly` or `Next1`.

## Lean Scope

Lean addition in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

It should start from

```text
F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

It starts from this theorem with `M := M+1`, then rewrites the remaining
`(fderiv Next0 z) v` using

```text
fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply
```

with `M := M+1` and `s := 0 : Fin (M+1)`.

## Kill Conditions

- Do not state this for arbitrary positive tail length `M+1`; the `M = 0`
  boundary has no successor index.
- Do not instantiate the successor theorem with `q := r0`; `r0` has the
  solved-factor index type, not the current-tail index type.
- Do not use tangent `v.1 q1`; the correct tangent is `v.1 u1`.
- Do not rewrite the first-level `dPsucc` even though the next-level `Pcast1`
  is value-wise related to it; that is a separate staging step.
- Do not commute matrix factors or distribute the outer
  `- dEarly * terminalSolvedA1`.
- Do not claim full positive-tail `F3` target staging, determinant equality,
  measure transport, normal crossings, pole order, or RLCT.

## Nonclaims

No full finite sum formula for `dEarly`, no expansion of `dPsucc1`, no terminal
cleanup of `Psucc1`, no determinant-one target-side linear equivalence, no
measure theorem, no normal crossings, no pole order, and no RLCT follows from
this slice.
