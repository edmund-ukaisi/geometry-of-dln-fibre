# Reproduction - A2 retained-passive edge-pair source-staged tuple assembly

Date: 2026-06-27.

Status: controller pen-and-paper reproduction before Lean formalisation.

This is a hybrid whole-tuple package.  Only the `(F2,C)` edge-family branch is
source-staged by the all-edge successor family.  The passive `A1`, `Ctop`, and
terminal `F3` entries remain the derivative-staged corrections from the
earlier tuple assembly.

## Setup

Let

```text
raw   = topologyTupleEdgeRawOrder,
coord = (ofTopologyTuple z).toCoordinateData,
Dzv   = d(raw)_z(v).
```

The existing derivative-staged tuple package is

```text
old = shearedTopologyTupleEdgeRawOrderFDerivAt z v.
```

It satisfies

```text
old = retainedPassiveFormalRawOrderJacobianAt z v.
```

The all-edge source-staged edge-pair package defines

```text
Xsucc = retainedPassiveSourceStagedSuccessorF2 v
```

and proves that the edge-family pair

```text
U_F(q) =
  Dzv.F2_q
  + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
  - Xsucc(q) * coord.C q,

U_C(q) =
  Dzv.C_q
  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc
```

equals the `(F2,C)` family of the same formal raw-order output.

## Hybrid Tuple

Define the hybrid tuple by keeping the old tuple everywhere except in the
edge-pair branch:

```text
edgePairSourceStagedSheared =
  ( old.A1passive,
    ( U_F,
      ( old.A3passive,
        ( U_C,
          ( old.Ctop,
            old.F3 )))))
```

The old `A1passive`, `A3passive`, `Ctop`, and `F3` components already equal
the corresponding formal components by the derivative-staged tuple theorem.
The new `U_F` and `U_C` components equal the corresponding formal edge-pair
components by the all-edge source-staged edge-pair theorem.  Product
extensionality gives the whole-tuple equality

```text
edgePairSourceStagedSheared
  = retainedPassiveFormalRawOrderJacobianAt z v.
```

## Boundary

The source-staging in this theorem is not target-side-only.  The family
`Xsucc` uses the source tangent `v.F2_(p.succ)` on nonterminal edges and the
terminal zero only at `Fin.last M`.  The entries outside `(F2,C)` have not
been source-staged:

- passive `A1` still contains derivative corrections involving successor
  `F2` and solved `A3`;
- `Ctop` still contains the first successor corrections and
  `d(Tail^{-1}) * Ctop`;
- `F3` still contains the early-tail and terminal-top derivative corrections.

## Kill Conditions

- If the theorem name or docstring suggests that the whole tuple is
  source-staged, it overclaims.
- If the theorem is read as a target-side `LinearEquiv`, determinant-one
  shear, actual derivative determinant equality, or measure transport, it
  overclaims.
- If `Xsucc` is treated as target-recovered data rather than a source tangent
  family, it overclaims.
- If the passive `A1`, `Ctop`, or `F3` entries are rewritten using the
  source-staged edge-pair theorem alone, the proof is invalid.

## Nonclaims

No target-side `LinearEquiv`, no determinant-one shear, no actual derivative
determinant formula, no measure transport, no normal crossings, no pole order,
and no RLCT follows from this hybrid tuple package.
