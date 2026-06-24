# Statement card - A4 selected-entry transition microcertificate evaluation

## Claim

The finite selected-entry normal-crossing microcertificate can be evaluated at
a target chart point produced by the finite source-to-target selected-entry
transition.  On the normalized target-coordinate overlap, the target chart
point has the same center value as the source chart point, so the loss
monomial identity can be read with the source-selected center square on the
left and the target chart coordinate/unit on the right.

## Lean Targets

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

## Source

- Aoyagi PDF pp. 19-22 for the Case 2 selected-entry residual-center chart.
- Existing A4 reproduction notes for the selected-entry microcertificate and
  transition point.

## Dependencies

- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate`
- `sourceChartTransitionPoint`
- `chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`
- Existing source-point loss/unit/Jacobian/monomial identities.

## Nonclaims

This is not analytic transition regularity, chart coverage, source production
of successor data, a volume-form theorem, a global A0 certificate, pole order,
or RLCT extraction.
