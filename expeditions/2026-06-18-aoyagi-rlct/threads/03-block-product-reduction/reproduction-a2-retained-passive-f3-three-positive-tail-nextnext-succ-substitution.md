# Reproduction - A2 retained-passive F3 three-positive-tail next-next successor substitution

Date: 2026-06-27.

Status: reproduced by controller; proved in Lean; independent xhigh checks
passed.

This note is independent of the quiver-based paper.  It records the next
consumer step after the two-positive-tail `F3` theorem whose first recursive
`Nextfun` successor recurrence was substituted.

## Setup

The landed two-positive-tail theorem writes the passive tail length as
`(M+1)+1` and leaves one deeper recursive derivative explicit:

```text
dNext1 = (fderiv NextNextfun z) v.
```

To expand this deeper derivative, the passive tail must have at least three
indices.  We therefore write the tail length as `((M+1)+1)+1` and instantiate
the two-positive-tail theorem with `M := M+1`.

The first two recursive positions are inherited from the landed theorem:

```text
q0 = 0                         : Fin (((M+1)+1)+1),
p0 = q0.castSucc               : Fin ((((M+1)+1)+1)+1),
r0 = q0.succ                   : Fin ((((M+1)+1)+1)+1),

s0 = 0                         : Fin ((M+1)+1),
q1 = s0.succ                   : Fin (((M+1)+1)+1),
u1 = s0.castSucc               : Fin (((M+1)+1)+1),
p1 = q1.castSucc               : Fin ((((M+1)+1)+1)+1),
r1 = q1.succ                   : Fin ((((M+1)+1)+1)+1).
```

The landed theorem expands the `q1` successor branch and leaves
`NextNextfun`, the lower-left product-tail sum starting at `p1.val+1`, as a
remaining derivative.

## Second Successor Reindexing

To expand `dNext1`, instantiate the same successor-index `dEarly` theorem one
level deeper.  In the helper theorem the source parameter has type
`s : Fin M`, and the current lower-left index is `q = s.succ`.  In the
ambient tail `((M+1)+1)+1`, the next current lower-left index is the second
successor, so set

```text
t0 = 0                         : Fin (M+1),
s1 = t0.succ                   : Fin ((M+1)+1),
q2 = s1.succ                   : Fin (((M+1)+1)+1),
u2 = s1.castSucc               : Fin (((M+1)+1)+1),
p2 = q2.castSucc               : Fin ((((M+1)+1)+1)+1),
r2 = q2.succ                   : Fin ((((M+1)+1)+1)+1).
```

Then `p2.val = p1.val+1`, so the helper theorem's `Tailfun` is exactly the
old `NextNextfun`.

The source tangent in the solved-`A1` derivative branch is `v.1 u2`, not
`v.1 q2`.  This follows from the successor theorem's identity

```text
u2.succ = s1.castSucc.succ = s1.succ.castSucc = q2.castSucc = p2.
```

Thus `v.1 u2` is the source tangent corresponding to the solved factor at
`p2`.

## Calculation

The second successor substitution replaces only the final summand of the
already expanded `dNext1`:

```text
dNext1 =
  -(((dCnext2) * C_r2 + Cnext2 * dC_r2) * A3p2 * Pcast2^-1)
  - (Cprod2 * dG2 * Pcast2^-1)
  + Cprod2 * A3p2 * Pcast2^-1
      * (dPsucc2 * solvedA1(p2) + Psucc2 * v.1 u2)
      * Pcast2^-1
  + dNext2.
```

Here

```text
dNext2 = (fderiv NextNextNextfun z) v,
```

and the first-level `dEarly` expression and terminal `dLast` target factor are
unchanged.  Substitution into the landed two-positive expression gives

```text
Dzv.F3
  - dEarly_expanded_two_successor_steps
      * coord.solvedA1(Fin.last (((M+1)+1)+1))
  + (coord.F3 - Early(z)) * dLast_target
  = formal.F3.
```

No distribution across the outer product
`- dEarly * coord.solvedA1(Fin.last (((M+1)+1)+1))` is part of this slice.

## Recovery Consumer

The recovery theorem uses the same staged `F3` expression.  Once the equality
theorem identifies this expression with the formal raw-order `F3` tangent, the
formal recovery theorem gives

```text
staged_F3 * (-(coord.solvedA1(Fin.last (((M+1)+1)+1))))^-1
  = source_F3_tangent.
```

The recovery consumer does not recurse further into `dNext2`.

## Lean Scope

Target file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Planned Lean names:

```text
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

Landed Lean names:

```text
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

Dependencies:

- `F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
```

passed.  `scripts/sorries` reported zero forbidden markers, `git diff --check`
was clean, the full `DLNFibre` build passed with only pre-existing style
warnings, and `#print axioms` for both new theorem names reported only
`[propext, Classical.choice, Quot.sound]`.  Xhigh pre-Lean index check and
post-Lean fidelity review passed in
`review-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`.

## Kill Conditions

- State the theorem only for tail length `((M+1)+1)+1`.
- Do not use tangent `v.1 q2`; the correct tangent is `v.1 u2`.
- Do not rewrite `dPsucc`, `dPsucc1`, or `dPsucc2`.
- Do not simplify terminal or empty-suffix cases.
- Do not commute factors or distribute the outer
  `- dEarly * terminalSolvedA1`.
- Do not claim full positive-tail `F3` target staging, determinant equality,
  measure transport, normal crossings, pole order, or RLCT.
