# Review - A2 product-step full formal linear maps

Date: 2026-06-26.

Reviewers: controller plus xhigh read-only reviewers `Tesla` and
`Chandrasekhar`.

## Verdict

Pass for the bundled-linear-map checkpoint. The Lean construction proves
linearity by construction from fixed left/right matrix multiplication maps,
not by an expanded monolithic `map_add`/`map_smul` proof.

## Mathematical Check

At a fixed base point, every term in the full p. 13 tangent formulas is a fixed
coefficient matrix multiplying exactly one tangent component on the left and/or
right. Sums and differences of these terms are linear. The inverse formula has
the same property.

The reviewers also emphasized that the native raw and chart tuple orders still
differ, so no determinant should be taken before composing with the existing
chart-output raw-order equivalence.

## Lean/API Check

The implementation imports `Mathlib.Data.Matrix.Bilinear` and uses
`mulLeftLinearMap` and `mulRightLinearMap`, together with named nested-tuple
projections and `LinearMap.prod`. The application theorems expand the bundled
maps back to the reviewed tuple formulas; `Matrix.mul_assoc` accounts only for
parenthesization differences.

## Scope Check

This checkpoint does not prove inverse composition, a full `LinearEquiv`,
determinant unitness, analytic differentiability, source-measure pushforward,
density transport, normal crossings, pole order, or RLCT.
