# Reproduction - A2 product-step formal Jacobian A1 unit

Date: 2026-06-26.

Status: pen-and-paper reproduction for the finite formal tangent calculation.

## Question

The full p. 13 formal Jacobian determinant theorem was previously stated on
the raw determinant chart, with hypotheses `IsUnit C1.det` and
`IsUnit A1.det`.  The record-level coordinate inverse has now been separated
from that chart domain and only uses `IsUnit A1.det`.  This note checks the
same issue at the formal tangent level.

The question is:

```text
Does the full raw-order formal tangent map have unit determinant under only
IsUnit A1.det?
```

## Source Anchors

Aoyagi Lemma 2 and Theorem 3, PDF pp. 10-13.  The source-backed content is the
elementary one-step product-reduction coordinate change.  This note uses no
quiver-paper input.

The raw variables are ordered as

```text
(C1, D, F3old, A1, A2, A3, A4),
```

and the chart variables as

```text
(Ctop, D, A1, A3, F2, F3, C).
```

Let

```text
Q = C1 * A1.
```

The forward coordinate formulas are

```text
Ctop = Q,
D    = D,
A1   = A1,
A3   = A3,
F2   = - A1^-1 * A2,
F3   = F3old - D * A3 * Q^-1,
C    = A4 - A3 * A1^-1 * A2.
```

The inverse coordinate formulas are

```text
C1    = Ctop * A1^-1,
D     = D,
F3old = F3 + D * A3 * Ctop^-1,
A1    = A1,
A2    = - A1 * F2,
A3    = A3,
A4    = C - A3 * F2.
```

## Formal Tangent Formulas

For a raw tangent vector

```text
(dC1, dD, dF3old, dA1, dA2, dA3, dA4),
```

the forward formal tangent formula has

```text
dQ  = dC1 * A1 + C1 * dA1,
dF2 = A1^-1 * dA1 * A1^-1 * A2 - A1^-1 * dA2,
dF3 = dF3old
       - dD * A3 * Q^-1
       - D * dA3 * Q^-1
       + D * A3 * Q^-1 * dQ * Q^-1,
dC  = dA4
       - dA3 * A1^-1 * A2
       + A3 * A1^-1 * dA1 * A1^-1 * A2
       - A3 * A1^-1 * dA2.
```

For a chart tangent vector

```text
(eQ, eD, eA1, eA3, eF2, eF3, eC),
```

the inverse formal tangent formula has

```text
dC1    = eQ * A1^-1 - Q * A1^-1 * eA1 * A1^-1,
dF3old = eF3
          + eD * A3 * Q^-1
          + D * eA3 * Q^-1
          - D * A3 * Q^-1 * eQ * Q^-1,
dA2    = - eA1 * F2 - A1 * eF2,
dA4    = eC - eA3 * F2 - A3 * eF2.
```

All appearances of `Q^-1` are totalized inverses in the formal algebra.  The
automorphism calculation below does not use `Q * Q^-1 = 1`.

## Inverse After Forward

Substitute the forward tangent formula into the inverse tangent formula at the
raw-derived chart base point.

For the `dC1` component:

```text
(dQ * A1^-1) - Q * A1^-1 * dA1 * A1^-1
= (dC1 * A1 + C1 * dA1) * A1^-1
  - (C1 * A1) * A1^-1 * dA1 * A1^-1
= dC1 + C1 * dA1 * A1^-1 - C1 * dA1 * A1^-1
= dC1.
```

The only multiplicative cancellation is by `A1`.

For the old `dF3` component:

```text
(dF3old - dD * A3 * Q^-1 - D * dA3 * Q^-1
  + D * A3 * Q^-1 * dQ * Q^-1)
+ dD * A3 * Q^-1
+ D * dA3 * Q^-1
- D * A3 * Q^-1 * dQ * Q^-1
= dF3old.
```

This is additive cancellation.  It does not require `Q` to be invertible.

For `dA2`:

```text
-dA1 * (-A1^-1 * A2)
- A1 * (A1^-1 * dA1 * A1^-1 * A2 - A1^-1 * dA2)
= dA1 * A1^-1 * A2
  - (dA1 * A1^-1 * A2 - dA2)
= dA2.
```

For `dA4`:

```text
dA4 - dA3 * A1^-1 * A2
+ A3 * A1^-1 * dA1 * A1^-1 * A2
- A3 * A1^-1 * dA2
- dA3 * (-A1^-1 * A2)
- A3 * (A1^-1 * dA1 * A1^-1 * A2 - A1^-1 * dA2)
= dA4.
```

The remaining coordinates are definitionally unchanged.

## Forward After Inverse

For the top block,

```text
(eQ * A1^-1 - Q * A1^-1 * eA1 * A1^-1) * A1 + C1 * eA1
= eQ - C1 * eA1 + C1 * eA1
= eQ.
```

Again this only uses `A1^-1 * A1 = 1` and `Q * A1^-1 = C1`.

For `eF3`, after the recovered top tangent is `eQ`, all `Q^-1` terms cancel
additively:

```text
eF3 + eD * A3 * Q^-1 + D * eA3 * Q^-1
- D * A3 * Q^-1 * eQ * Q^-1
- eD * A3 * Q^-1 - D * eA3 * Q^-1
+ D * A3 * Q^-1 * eQ * Q^-1
= eF3.
```

For `eF2`,

```text
A1^-1 * eA1 * A1^-1 * A2
- A1^-1 * (-eA1 * (-A1^-1 * A2) - A1 * eF2)
= eF2.
```

For `eC`,

```text
eC - eA3 * (-A1^-1 * A2) - A3 * eF2
- eA3 * A1^-1 * A2
+ A3 * A1^-1 * eA1 * A1^-1 * A2
- A3 * A1^-1 * (-eA1 * (-A1^-1 * A2) - A1 * eF2)
= eC.
```

Thus the formal raw/chart tangent maps are inverse linear maps under only
`IsUnit A1.det`.

## Determinant Consequence

The native formal tangent map has chart-ordered codomain.  Compose it with the
already-defined coordinate permutation

```text
productReductionStepChartTangentRawOrderEquiv
```

to get a raw-order endomorphism.  Since the raw/chart formal tangent map is a
linear equivalence under `IsUnit A1.det`, and the reorder is a linear
equivalence, their composition is a linear automorphism.  In finite raw
tangent coordinates, `LinearMap.det` of this endomorphism is therefore a unit.

## Lean Shape

Add A1-only variants:

```text
productReductionStepFormalJacobianInverseFormula_formula_chartBase_of_isUnit_A1
productReductionStepFormalJacobianFormula_inverseFormula_chartBase_of_isUnit_A1
productReductionStepFormalJacobianEquiv_of_isUnit_A1
productReductionStepFormalJacobianEquiv_of_isUnit_A1_apply
productReductionStepFormalJacobianEquiv_of_isUnit_A1_symm_apply
productReductionStepFormalJacobianRawOrderEquiv_of_isUnit_A1
productReductionStepFormalJacobianRawOrderEquiv_of_isUnit_A1_apply
productReductionStepFormalJacobianRawOrder_det_isUnit_of_isUnit_A1
```

Keep the old determinant-chart names as wrappers so existing derivative and
measure APIs still advertise the correct analytic domain.

## Labels

- Proved: finite formal raw/chart tangent equivalence and raw-order
  determinant unitness under `IsUnit A1.det`.
- Assumed: finite side-index hypotheses for the determinant theorem.
- Cited: Aoyagi pp. 10-13 only for the elementary one-step coordinate
  formulas.
- Deferred: analytic derivative validity outside determinant-chart domains,
  source-chart production, source coverage, source-measure transport,
  density/Jacobian identity for the original DLN source, normal crossings,
  pole order, and RLCT.

## Nonclaims

- This is not a nonlinear analytic derivative theorem.
- This does not weaken the determinant-chart hypotheses for analytic
  derivative or measure statements.
- This does not say `C1 * A1` is invertible from `A1` alone.
- This does not prove a local source chart, source-rank coverage,
  source-measure pushforward, density transport, normal crossings, pole order,
  or RLCT extraction.
