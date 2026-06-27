# A2 Retained-Passive Formal Raw-Order Absolute Determinant

Status: controller reproduced; Lean target selected.

## Scope

This note records the absolute-value simplification of the already-proved
formal raw-order determinant formula.  It is finite linear algebra in the
retained-passive `TopologyTuple` product order.  It does not identify the
formal map with the analytic Frechet derivative of `topologyTupleEdgeRawOrder`,
and it does not prove a measure pushforward, source-prior identity, normal
crossing, pole order, or RLCT statement.

## Input Formula

The existing formal raw-order theorem states

```text
det J_formal =
  det(Tail^-1)^|rho|
  * product_p det(-A p)^|kappa' p.castSucc|
  * det(-LastTop)^|kappa' last|
```

where:

- `Tail` is the solved first-edge top-left tail;
- `A p` is the solved top-left block at edge `p`;
- `LastTop` is the terminal top-left block acting on the final `F3` variable.

The point-specialized bridge reads these from a tuple `z` as

```text
Tail    = retainedPassiveA1TailAfterFirst data.A1seed
A p     = coord.solvedA1 p
LastTop = coord.solvedA1 (Fin.last M)
```

with `data = ofTopologyTuple z` and `coord = data.toCoordinateData`.

## Absolute-Value Calculation

Taking absolute values gives

```text
|det J_formal| =
  |det(Tail^-1)|^|rho|
  * product_p |det(-A p)|^|kappa' p.castSucc|
  * |det(-LastTop)|^|kappa' last|.
```

For a square matrix over `R`,

```text
det(-A) = (-1)^n det(A),
```

so

```text
|det(-A)| = |det(A)|.
```

Thus the formal absolute determinant is

```text
|det J_formal| =
  |det(Tail^-1)|^|rho|
  * product_p |det(A p)|^|kappa' p.castSucc|
  * |det(LastTop)|^|kappa' last|.
```

This is the sign-free version needed by any later density comparison.  It
intentionally does not replace the analytic density
`topologyTupleEdgeRawOrderFDerivAbsDet`; that comparison still requires a
separate formal-to-analytic derivative theorem.

## Lean Targets

Generic formal raw-order theorem:

```lean
retainedPassiveFormalRawOrderJacobian_abs_det_eq
```

Point-specialized tuple theorem:

```lean
retainedPassiveFormalRawOrderJacobianAbsDetAt_eq
```

## Guardrails

- Do not use this theorem as `topologyTupleEdgeRawOrderFDerivAbsDet_eq`.
- Do not remove any source-prior, chart-image, or local-source hypotheses with
  this theorem.
- Keep `LastTop` as the terminal solved top block, not the first-edge tail.
