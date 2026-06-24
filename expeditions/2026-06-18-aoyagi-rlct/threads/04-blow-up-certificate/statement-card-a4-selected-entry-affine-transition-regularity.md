# Statement card - A4 selected-entry affine transition regularity

## Lean target

Planned file:
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.

Planned names:

```text
SelectedEntryFiniteAffineTransitionRegularPair
SelectedEntryFiniteAffineTransitionRegularFamily
SelectedEntryFiniteAffineTransitionRegularFamily.pair
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.finiteAffineTransitionRegular
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finiteAffineTransitionRegular
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finiteAffineTransitionRegular_displayedPair
```

## Claim

For the finite selected-entry all-pivot chart family, the overlap between a
source pivot chart and a target pivot chart has the concrete affine transition

```text
u_target = u_source * normalized_source(target_pivot),
residual_target(i) = normalized_source(i) / normalized_source(target_pivot),
```

on the normalised target-coordinate open condition
`normalized_source(target_pivot) != 0`.  These formulas preserve the finite
chart map, have the expected inverse, and satisfy the finite cocycle identity
on triple overlaps.

## Inputs

- A finite center set with a chart enumeration.
- A source chart and target chart.
- Field-valued selected-entry coordinates.
- Nonzero normalised target denominator for the overlap-dependent fields.

## Outputs

- A concrete finite affine-overlap family predicate inhabited by the
  selected-entry chart formulas.
- A pair extraction theorem and Case 2 residual-block/displayed-target
  specialisations.

## Nonclaims

No analytic chart coverage, no analytic regular-map theorem, no unit
regularity, no analytic Jacobian compatibility, no source production, no
branch termination, no normal crossings, no pole order, and no RLCT extraction.

The predicate is finite selected-entry overlap algebra only, but it is not a
trivial predicate: its fields are the actual transition-point, coordinate,
chart-map, inverse, self-transition, and cocycle identities.  It can instantiate
a finite selected-entry transition predicate only when that predicate is
explicitly chosen to mean these algebraic overlap identities.
