# Review - A2 product-step full formal Jacobian equivalence

Date: 2026-06-26.

Reviewers: controller plus xhigh read-only reviewers `Tesla` and
`Chandrasekhar`.

## Verdict

Pass for the finite formal-equivalence checkpoint.  The forward and inverse
formula-composition proofs are componentwise and avoid the previous monolithic
`ext <;> simp` proof shape that timed out.

## Mathematical Check

The only multiplicative inverses used are the determinant-chart inverses of
`A1` and `Q=C1*A1`.  The `Q` inverse appears in the `dF3` component only in
matching add/subtract pairs, so no extra determinant hypothesis on `D`, `A3`,
or `C` is introduced.  The `dCtop`, `dF2`, and `dC` components use the standard
finite matrix cancellations `A1*A1^-1=1`, `A1^-1*A1=1`, and
`(C1*A1)*A1^-1=C1`.

The sign checks agree with the p. 13 formulas: the inverse-variation term in
`dF3` has positive sign in the forward formula, while the `dD` and `dA3` terms
have negative sign; the `dA2` and `dC` branches both use `F2=-(A1^-1*A2)`.

## Lean/API Check

The Lean proof first proves two tuple-valued formula-composition theorems:

```text
productReductionStepFormalJacobianInverseFormula_formula_chartBase
productReductionStepFormalJacobianFormula_inverseFormula_chartBase
```

The bundled equivalence is then a short `LinearEquiv.ofLinear` wrapper using
the existing apply theorems for the forward and inverse `LinearMap`s.  This is
the right API layer: subsequent determinant work can use the equivalence
without reopening the component algebra.

## Scope Check

This checkpoint does not prove determinant unitness for the full Jacobian.  The
raw and chart tuple orders differ, so the determinant theorem must still pass
through the chart-output raw-order equivalence.  It also does not prove
analytic differentiability, source-measure pushforward, density transport,
normal crossings, pole order, or RLCT.
