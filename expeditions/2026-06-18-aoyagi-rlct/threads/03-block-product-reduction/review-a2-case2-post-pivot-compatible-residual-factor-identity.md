# Review - A2 Case 2 post-pivot compatible residual-factor identity

Date: 2026-06-26.

Reviewers: controller, xhigh source scout `Godel the 2nd`, and xhigh Lean/API
scout `Bacon the 2nd`.

## Verdict

Pass for a negative audit. The proposed source-backed identity should be
killed unless the entrywise successor readout is supplied as an explicit
hypothesis.

## Source Check

The source scout checked Aoyagi PDF pp. 19-21. The paper prints the Case 2
selected-entry substitution for the current residual block, the regular
`Q` and `P` operations, the transformed following factor `C' = Q^-1 C`, the
cleared block `D''' = blockdiag(1,D_(J+1))`, and the lower product
`D_(J+1) * C'_+`.

The paper does not print an equation saying that this lower product is the
successor selected-entry chart-map matrix. The source-backed entrywise formula
is the finite sum

```text
sum_k (Z_ik - x_i y_k) C_(k,a).
```

Turning that finite sum into `CenterCoord.chartMap pivotNext yNext (i,a)` is a
new readout/source-production assertion.

## Lean/API Check

The Lean/API scout confirmed that the finite product layer is already covered:

```text
case2PostPivotTwoEdgeDomain
case2PostPivotFreeTwoEdgeFactorFamily
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_paperCprime_eq_sourceResidualBlock_successorFollowingFactor
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
```

The remaining live hypothesis is the entrywise successor readout `hentry`. An
adapter theorem from a source-product entrywise readout would be low risk, but
it would still be a conditional wrapper and should not be the next
source-moving target.

Post-recovery Lean/API recheck sharpened the obstruction.  Fixed-chart inverse
lemmas require a nonzero fixed pivot, while current all-pivot coverage can
choose some pivot and does not prove that the successor fixed pivot
`(J+2,J+2)` is nonzero for the post-pivot product.  Defining `yNext` as an
inverse chart point for `D_(J+1) * C'_+` would therefore require additional
finite hypotheses and would still not be Aoyagi source production.

## Guardrails

- Keep the successor center at `(S,J+1)` with pivot `(J+2,J+2)`.
- Do not identify the old center `(S,J)` with the successor center.
- Do not treat `D_(J+1) * C'_+` as a selected-entry center matrix without an
  explicit entrywise readout.
- Do not replace the entrywise readout by all-pivot coverage unless a theorem
  chooses the fixed successor pivot and proves its nonvanishing.
- Do not claim source production of `Cprime`, `Csucc`, `yNext`, endpoint
  equivalences, source/image equality, normal crossings, pole order, or RLCT.
