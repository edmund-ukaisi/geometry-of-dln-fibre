# Reproduction - A2 retained-passive target edge-pair linear map

Date: 2026-06-28.

Status: controller pen-and-paper reproduction for the first target-side
component packaging rung.

This note is Aoyagi-only and independent of the quiver-based paper.  It records
the finite linear-algebra content needed to package the already-defined
target-side all-edge `(F2,C)` shear as a linear map in the target raw tuple.
It does not construct a target normalizer or a determinant theorem.

## Fixed data

Fix a retained-passive tuple `z` and write its coordinate data as

```text
coord = ofTopologyTuple(z).toCoordinateData.
```

The target variable is an arbitrary raw tuple `w`.  All matrices below that
come from `coord` are constants with respect to `w`.  The raw block readouts

```text
w |-> w.F2(q),
w |-> w.C(q),
w |-> rawEdgeTupleA1(w,q),
w |-> rawEdgeTupleA3(w,q)
```

are coordinate projections, hence linear in `w`.

## Backward recovered F2 recurrence

The existing function `retainedPassiveTargetRecoveredF2At z w` is defined by
reverse induction over `q : Fin (M+1)`.

At the terminal edge `q = last`, it has the form

```text
X_last(w)
  = A_last^{-1} *
      (H_last * (C_w(last) + G_w(last) * F2_z(last.castSucc))
       - (F_w(last) + A_w(last) * F2_z(last.castSucc))).
```

Here `A_last`, `H_last`, and `F2_z(last.castSucc)` are fixed by `z`; the four
`w` terms are linear readouts.  Matrix multiplication by a fixed matrix on the
left or right distributes over addition and scalar multiplication.  Therefore
`X_last(w+w') = X_last(w)+X_last(w')` and
`X_last(a*w) = a*X_last(w)`.

At a nonterminal edge `q = p.castSucc`, the recurrence is

```text
X_q(w)
  = A_q^{-1} *
      (H_q * (C_w(q) + G_w(q) * F2_z(q.castSucc))
       - (F_w(q) + A_w(q) * F2_z(q.castSucc) - X_succ(w) * C_z(q))).
```

The successor term is the cast of the already recovered value
`X_{p.succ}(w)`.  The cast is a linear equivalence.  Thus, if the successor
value is linear in `w`, the displayed formula is again a sum of linear terms
and fixed left/right multiplications.  Reverse induction proves every
`X_q(w)` is linear in `w`.

## Successor family

The successor family is

```text
Xsucc(p.castSucc,w) = cast (X_{p.succ}(w)),
Xsucc(last,w)       = 0.
```

The nonterminal branch is a linear cast of a linear recovered value, and the
terminal branch is the zero linear map.  Hence the whole successor family is a
linear map from the raw tuple to the dependent product of successor matrices.

## Edge-pair shear

The existing target edge-pair shear is

```text
U_F(q,w)
  = w.F2(q)
      + rawEdgeTupleA1(w,q) * F2_z(q.castSucc)
      - Xsucc(q,w) * C_z(q),

U_C(q,w)
  = w.C(q)
      + rawEdgeTupleA3(w,q) * F2_z(q.castSucc).
```

Each term is linear in `w`: `w.F2`, `w.C`, `rawEdgeTupleA1`, and
`rawEdgeTupleA3` are projections, while multiplication by
`F2_z(q.castSucc)` and `C_z(q)` is by fixed matrices.  The successor family was
proved linear above.  Therefore

```text
w |-> (q |-> U_F(q,w), q |-> U_C(q,w))
```

is a linear map from the retained-passive raw tuple space to the separated
all-edge `(F2,C)` family space.

## Lean target

Expected Lean names in `RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetRecoveredF2LinearMapAt
retainedPassiveTargetRecoveredF2LinearMapAt_apply
retainedPassiveTargetRecoveredSuccessorF2LinearMapAt
retainedPassiveTargetRecoveredSuccessorF2LinearMapAt_apply
retainedPassiveTargetEdgePairShearLinearMapAt
retainedPassiveTargetEdgePairShearLinearMapAt_apply
```

## Kill Conditions

- Do not claim a `LinearEquiv`; only a `LinearMap` is reproduced here.
- Do not claim determinant one or absolute determinant one.
- Do not claim the whole retained-passive target normalizer has been
  constructed.
- Do not claim determinant equality for `topologyTupleEdgeRawOrder`, measure
  transport, normal crossings, pole order, RLCT, or analytic extraction.
