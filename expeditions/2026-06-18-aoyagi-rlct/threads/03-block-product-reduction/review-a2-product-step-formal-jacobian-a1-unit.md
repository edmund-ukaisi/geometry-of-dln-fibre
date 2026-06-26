# Review - A2 product-step formal Jacobian A1 unit

Date: 2026-06-26.

Reviewers: controller plus xhigh Lean/API reviewer `McClintock the 2nd`.

## Verdict

Pass.  The new A1-only formal tangent equivalence and determinant-unit theorem
are correctly scoped as finite formal algebra.

## Mathematical Check

The new proofs require only

```text
IsUnit x.A1.det.
```

All multiplicative cancellations are cancellations by `A1`.  The terms
containing `(x.C1 * x.A1)^-1` occur in matching additive pairs in the `dF3`
and `F3` components, so the proof does not use a hidden hypothesis that
`x.C1 * x.A1` is invertible.

The raw-order determinant statement still first composes the native
raw-to-chart formal tangent map with

```text
productReductionStepChartTangentRawOrderEquiv.
```

Thus the determinant is taken only for a raw-shaped endomorphism, and unitness
comes from `LinearEquiv.isUnit_det'` applied to a linear automorphism.

## Lean/API Check

New A1-only names:

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

The old determinant-chart names are preserved as wrappers with the same
visible `hC1 hA1` call shape.  This avoids breaking downstream derivative and
measure files that intentionally work on determinant-chart hypotheses.

Focused module build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
```

The xhigh reviewer additionally checked direct Lean elaboration of
`ProductReductionStepJacobian.lean`, `ProductReductionStepDerivative.lean`,
and `ProductReductionStepMeasure.lean`, plus `git diff --check` for the Lean
file.

## Scope Check

No analytic derivative, source-measure pushforward, density transport, source
coverage, normal-crossing, pole-order, or RLCT claim is introduced.  In
particular, this does not weaken the determinant-chart hypotheses needed by
the analytic derivative and measure-change APIs.
