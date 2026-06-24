# Reproduction - A4 selected-entry transition microcertificate evaluation

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised and reviewed.

## Source Anchor

Aoyagi PDF pp. 19-22 uses the Case 2 selected-entry blow-up chart for the
finite residual-block center.  Earlier A4 notes already isolated the elementary
selected-entry chart family, the finite transition point between two selected
pivots, and the one-coordinate microcertificate for the finite center
square-sum and formal pivot-first determinant.

This note only combines those already-reproduced finite facts.  It evaluates
the microcertificate's loss, loss unit, formal Jacobian/prior, and monomial
identities at a target chart point produced from a source chart by the finite
selected-entry transition.

## Pen-and-Paper Calculation

Let `E` be a finite center and let `p,q in E` be the source and target pivots.
In the source chart write

```text
x_e = u * z_e,
z_p = 1,
z_e = residual(e)  for e != p.
```

On the overlap where the source-normalized target coordinate is nonzero,

```text
z_q != 0,
```

the target chart point is

```text
u_q = u * z_q,
y_e = z_e / z_q.
```

Then for every center coordinate

```text
u_q * y_e = (u * z_q) * (z_e / z_q) = u * z_e,
```

so the target chart map and source chart map give the same finite center value.
Therefore the certificate loss, which is a function of that center value, has

```text
loss(chartMap_q(target point))
  = sum_E (u * z_e)^2.
```

The loss unit at the target point is not the source unit.  It is the target
pivot's normalized square-sum factor,

```text
1 + sum_(e in E \ {q}) y_e^2.
```

The formal Jacobian/prior at the target point is likewise the target
pivot-first determinant,

```text
u_q ^ |E \ {q}|.
```

Thus the existing microcertificate monomial identities can be read at the
transition-generated target point:

```text
sum_E (u * z_e)^2
  = lossUnit_q(target point) * u_q^(2 * 1),

u_q ^ |E \ {q}|
  = jacobianPriorUnit_q(target point) * u_q^|E \ {q}|.
```

The nonzero hypothesis is only needed to identify the target chart map with the
source chart map, hence to make the loss identity source-facing.  The target
loss-unit and target formal determinant evaluations are definitional once the
target transition point is constructed, because division by zero is still a
total field operation in Lean.

## Case 2 Specialization

For Aoyagi Case 2,

```text
E = case2ResidualBlockPivotEntries n S J.
```

The all-pivot finite certificate enumerates `E` by

```text
finsetSubtypeChartEquiv E.
```

If `sourceChart` selects pivot `p` and `targetChart` selects pivot `q`, then
the source-facing loss after target transition is

```text
selectedEntryCenterSq E
  (case2SourceSelectedChartMapOfMem p_mem u residual).
```

The target unit and target formal determinant use

```text
denom = case2SourceSelectedNormalizedMapOfMem p_mem residual q,
targetU = u * denom,
targetResidual(r) =
  case2SourceSelectedNormalizedMapOfMem p_mem residual r / denom.
```

This gives a small local bridge from the transition-point algebra to the
chart-certificate fields.  It is deliberately local to the residual-center
square-sum and formal selected-entry determinant.

## Intended Lean Names

Generic selected-entry family:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartTransitionPoint_eq_centerSq_of_target_normalized_ne_zero
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartTransitionPoint_eq
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartTransitionPoint_eq_det
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartTransitionPoint_of_target_normalized_ne_zero
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartTransitionPoint
```

Case 2 all-pivot residual-block certificate:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartTransitionPoint_eq_sourceSelectedCenterSq_of_target_normalized_ne_zero
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartTransitionPoint_eq_sourceSelectedUnitFactor
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartTransitionPoint_eq_sourceSelectedDet
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartTransitionPoint_sourceSelected_of_target_normalized_ne_zero
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartTransitionPoint_sourceSelected
```

## Boundary

- This is finite selected-entry chart algebra.
- The loss identity is source-facing only on the normalized target-coordinate
  overlap.
- The unit and determinant are target-chart quantities after transition, not
  source-chart quantities.
- No analytic chart coverage, open-neighbourhood gluing, analytic transition
  regularity, Jacobian/volume-form theorem, normal crossings, pole order, or
  RLCT extraction is proved.
- No successor following factor, suffix product, recurrence post-data, or
  global A0 normal-crossing certificate is source-produced.

## Kill Conditions

- Do not replace the denominator `z_q` by `u*z_q` in the overlap hypothesis.
- Do not rewrite the target loss unit as the source loss unit unless a separate
  transition-unit theorem is proved.
- Do not read the formal pivot-first determinant as an analytic Jacobian
  theorem.
- Do not use this local residual-center calculation as a full DLN loss
  monomial identity.
