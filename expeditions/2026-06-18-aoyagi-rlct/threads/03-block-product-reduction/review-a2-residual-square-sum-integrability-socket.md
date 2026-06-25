# Review - A2 residual square-sum integrability socket

Date: 2026-06-25.

Reviewer: xhigh `Nash the 4th`.

Status: passed after low-severity wording fixes.

## Scope

Reviewed the square-sum socket in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

especially:

```text
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

and the accompanying reproduction, statement card, and memory updates.

## Findings

Low: the statement card wrote `b : alpha -> eta -> R`, which could be read as
a generic scalar-ring theorem, while the Lean theorem is real-valued.  It also
used `R` near `ball(0,R)`, overloading the radius notation.

Resolution: changed the statement card to `b : α -> η -> ℝ` and used `ρ` for
the ball radius.

Low: phrases such as "analytic regular-square product theorem" and
"regular-square product lower integral" could be misread as claiming
regular-coordinate additivity or a p.13 analytic-chart theorem.

Resolution: changed those phrases to "variable-base square-model product
estimate" and "square-model product lower integral".

No high- or medium-severity issue was found.

## Soundness Notes

The residual-block specialization keeps both strict positivity and residual
base lower-integral finiteness as explicit hypotheses.  The proof is only the
specialization

```text
b := fun x => AoyagiResidualBlockCoordinateIndex.value (D x)
```

in the coordinate-square-sum theorem.  It does not silently prove positivity,
nonvanishing of the residual square-sum, or residual negative-power
integrability.

Import hygiene is correct: the new module imports the coordinate definitions
and the analytic estimate layer, and `DLNFibre.lean` imports the new module
after those dependencies.

## Boundary

This is a square-sum socket theorem only.  It does not prove positivity or
negative-power integrability for Aoyagi's reduced residual coordinates, does
not cover a positive-measure zero set, and does not prove endpoint/divergence,
threshold equality, bounded-density/prior transport, p.13 analytic
chart/Jacobian construction, normal crossings, pole order, or RLCT.
