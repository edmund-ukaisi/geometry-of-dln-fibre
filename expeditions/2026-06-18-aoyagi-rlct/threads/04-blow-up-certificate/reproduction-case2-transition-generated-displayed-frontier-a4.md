# Reproduction - A4 Case 2 transition-generated displayed frontier

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; xhigh reviewed.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The displayed top-left pivot chart uses the
selected residual-block coordinate `(J+1,J+1)` and then applies the displayed
`Q/P` calculation and continuing/stopped frontier bookkeeping.

This note records the finite overlap version needed when the current
all-pivot selected-entry source chart is not already the displayed top-left
chart.

## Reproduction

Let `p` be the source all-pivot chart pivot and let the displayed target pivot
be

```text
q = (J+1,J+1).
```

Write the source-normalized residual-block coordinates as

```text
x_rs = case2SourceSelectedNormalizedMapOfMem p_mem residual (r,s).
```

Assume the displayed normalized coordinate is nonzero:

```text
d = x_(J+1,J+1) != 0.
```

The selected-entry transition to the displayed chart is

```text
targetU = u*d,
targetResidual_rs = x_rs/d.
```

Then the displayed chart map represents the same finite center values as the
original source chart point:

```text
targetU * targetResidual_rs = (u*d)*(x_rs/d) = u*x_rs.
```

The displayed top-left coordinate itself becomes

```text
targetResidual_(J+1,J+1) = d/d = 1,
```

in the normalized selected-entry chart, while the selected variable in the
displayed source-chart frontier package is `targetU`.

Therefore every already-proved displayed source-chart frontier theorem can be
instantiated at the transition-generated displayed data
`(targetU, targetResidual)`.  In particular:

1. the finite chart map of the displayed transition point equals the original
   source chart map;
2. the transition-generated displayed data satisfy the displayed source-chart
   frontier package;
3. under the continuing guard `J+2 <= M(S+1)`, the same data satisfy the
   displayed continuing reindexed source-chart certificate.

## Lean Targets

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.displayedChartIndex
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finsetSubtypeChartEquiv_displayedChartIndex
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_frontierBoundaryPackages_of_displayed_normalized_ne_zero
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingCertificate_of_displayed_normalized_ne_zero
```

## Boundary

- The denominator is the normalized displayed coordinate `d = x_(J+1,J+1)`,
  not the finite center value `u*d`.
- The target data are the transition-generated displayed chart coordinates.
- The displayed frontier and continuing certificate are existing finite
  source-chart packages instantiated at those target data.
- This proves no analytic transition regularity, no open-neighbourhood
  gluing, no chart coverage, no source-displayed all-pivot atlas, no
  source-produced global successor object, no suffix production, no analytic
  Jacobian/volume theorem, no global normal crossings, no pole order, and no
  RLCT extraction.
- This is not the separate substitution-block rewrite saying the
  transition-generated displayed substitution block equals the source-side
  selected-entry substitution block.

## Kill Conditions

- Do not replace `d != 0` by `(u*d) != 0`.
- Do not claim the complementary overlap where `d = 0` is handled.
- Do not read the displayed target frontier package as source production of
  arbitrary `Csucc` or `C'^(S+1)`.
- Do not infer chart regularity or transition regularity from the finite
  chart-index helper.
- Do not use all-pivot chart indices as evidence that Aoyagi prints every
  pivot chart.
