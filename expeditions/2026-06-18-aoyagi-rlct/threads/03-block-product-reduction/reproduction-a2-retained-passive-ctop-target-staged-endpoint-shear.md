# Reproduction - A2 retained-passive Ctop target-staged endpoint shear

Date: 2026-06-27.

Status: Lean proved; focused and full builds passed; sorry/whitespace/axiom
audits passed; independent xhigh checker passed.

This note is independent of the quiver-based paper.  It target-stages the
successor-edge part of the retained-passive `Ctop` correction using the
target-recovered successor `F2` family and the raw lower-left target readout.
It keeps the existing zero/positive tail split and the explicit suffix-tail
derivative term.  It is not a determinant theorem.

## Setup

Work at a retained-passive raw tuple `z` in the determinant chart, with tangent
`v`.  Write

```text
raw    = topologyTupleEdgeRawOrder,
coord  = (ofTopologyTuple z).toCoordinateData,
Dzv    = d(raw)_z(v),
formal = retainedPassiveFormalRawOrderJacobianAt(z)(v).
```

For the first retained edge put

```text
q0 = 0 : Fin (M+1).
```

The already-proved Ctop endpoint formulas are split by tail length.

For `M = 0`, the empty-tail formula is

```text
Dzv.Ctop
  - XsuccF2(q0) * coord.solvedA3(q0)
  - coord.F2(q0.succ) * XsuccA3(q0)
= formal.Ctop.
```

For `0 < M`, with `q : Fin M = 0`, `p = q.succ`, and

```text
Psucc(y) = residualFactorProduct(A1seed(y), Fin.last(M+1), p.succ),
```

the positive-tail formula is

```text
Dzv.Ctop
  - XsuccF2(q0) * coord.solvedA3(q0)
  - coord.F2(q0.succ) * XsuccA3(q0)
  + Tail^{-1} *
      (d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_q) *
      Tail^{-1} * coord.Ctop
= formal.Ctop.
```

Here `XsuccF2` and `XsuccA3` are source-staged successor families.

## Target-Side Replacements

The previous target edge-pair recovery slice proves, on actual derivative
targets,

```text
targetXsuccF2 = XsuccF2,
```

where

```text
targetXsuccF2 =
  retainedPassiveTargetRecoveredSuccessorF2At(z,Dzv).
```

The previous passive `A1` target-staged slice proves the lower-left replacement
for every edge `q`:

```text
coord.F2(q.succ) * rawEdgeTupleA3(Dzv,q)
  = coord.F2(q.succ) * XsuccA3(q).
```

Use this only at `q = q0`.  If `M = 0`, then `q0 = Fin.last 0`, and
`rawEdgeTupleA3(Dzv,q0)` is the terminal lower-left target derivative.  The
replacement is still valid because the multiplier is the terminal zero
extended `F2` slot.  No standalone terminal lower-left derivative identity is
used.

## Target-Staged Ctop Formulas

Substituting the two target-side replacements into the source-staged Ctop
formulas gives the target-staged zero-tail formula

```text
Dzv.Ctop
  - targetXsuccF2(q0) * coord.solvedA3(q0)
  - coord.F2(q0.succ) * rawEdgeTupleA3(Dzv,q0)
= formal.Ctop
```

for `M = 0`, and the positive-tail formula

```text
Dzv.Ctop
  - targetXsuccF2(q0) * coord.solvedA3(q0)
  - coord.F2(q0.succ) * rawEdgeTupleA3(Dzv,q0)
  + Tail^{-1} *
      (d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_q) *
      Tail^{-1} * coord.Ctop
= formal.Ctop
```

for `0 < M`.

Applying the already-proved formal recovery theorem for `Ctop` gives recovery
after left multiplication by `Tail`:

```text
Tail * (target-staged Ctop expression) = v.Ctop.
```

## Boundary Cases

- If `M = 0`, the positive-tail theorem is absent and the zero-tail theorem
  handles the empty product directly.
- In the `M = 0` zero-tail case, `q0` is terminal.  The raw lower-left target
  derivative is not zero; the product is killed by `coord.F2(q0.succ) = 0`.
- In the positive-tail case, the suffix derivative remains explicit.  This
  slice does not iterate the tail recurrence to a finite sum.
- The determinant-chart hypothesis is still required by the recovered
  successor `F2`, formal equality, and formal `Ctop` recovery theorems.

## Kill Conditions

- If `rawEdgeTupleA3(Dzv,q0) = XsuccA3(q0)` is asserted without the
  `coord.F2(q0.succ)` multiplier, the proof overclaims at `M = 0`.
- If the successor `F2` correction is the source-staged family rather than
  `retainedPassiveTargetRecoveredSuccessorF2At z Dzv`, the result is only the
  already-landed source-staged Ctop endpoint theorem.
- If the positive-tail theorem drops or commutes the explicit suffix derivative
  term, the noncommutative product-rule bookkeeping is wrong.
- If the result is read as `F3` target staging, whole-tuple target-side
  normalization, determinant-one target-side `LinearEquiv`, determinant
  equality, measure transport, normal crossings, pole order, or RLCT, it
  overclaims.

## Nonclaims

No `F3` target staging, no whole-tuple target-side normalization, no
determinant-one target-side `LinearEquiv`, no actual derivative determinant
formula, no measure transport, no normal crossings, no pole order, and no RLCT
follows from this Ctop target-staged endpoint shear.
