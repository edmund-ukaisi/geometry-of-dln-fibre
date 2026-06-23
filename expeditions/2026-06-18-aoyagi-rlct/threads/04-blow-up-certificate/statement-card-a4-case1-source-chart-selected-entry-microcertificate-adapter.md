# Statement card - A4 Case 1 source-chart selected-entry microcertificate adapter

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Generic names:

- `selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint`
- `selectedEntryCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq`
- `selectedEntryCenterSqFormalJacobianChartCertificate.loss_sourceChartPoint_eq_centerSq`
- `selectedEntryCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq`
- `selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPrior_sourceChartPoint_eq_det`
- `selectedEntryCenterSqFormalJacobianChartCertificate.loss_monomial_sourceChartPoint`
- `selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPrior_monomial_sourceChartPoint`

Case 1 namespaces:

- `case1SelectedOldCenterSqFormalJacobianChartCertificate`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate`

Each Case 1 namespace has the same seven source-point, chart-map, loss, unit,
determinant, and monomial identity names.

## Claim

The finite Case 1 selected-entry source chart points can be evaluated inside
the existing one-chart selected-entry normal-crossing microcertificate.  This
is proved for the selected-old finite `Unit` pivot and the displayed
row-strip pivot `(J+1,J+1)`.

## Inputs Kept Explicit

- ordered field coefficient type;
- Case 1 center parameters `n`, `S`, `J`, `J1`;
- for the displayed row-strip pivot, `1 <= J1` and `J+1 <= n(S+1)`;
- selected variable `u`;
- ambient finite-center residual function
  `residual : Case1CenterGenerator -> K`.

## Proved

Lean constructs the source chart point `(u, residual|_{E \\ {p}})` and proves
that the microcertificate chart map is the selected-entry chart map.  It also
proves that the loss is the finite Case 1 center square-sum, the loss unit is
the normalized square-sum factor, and the Jacobian/prior value agrees with
the formal pivot-first determinant.  The final monomial lemmas restate the
microcertificate loss and Jacobian/prior identities at those source chart
points.

## Not Proved

No source production of the hidden selected-old label, no chart coverage, no
transition regularity, no analytic unit neighbourhood, no analytic Jacobian or
volume-form theorem, no total DLN loss monomial identity, no global A0 chart
family, no active-ratio lower bound, no chart-count theorem, no pole order,
and no RLCT extraction.

## Verification

Independent review passed:

- `review-case1-source-chart-selected-entry-microcertificate-adapter-a4.md`

Controller gates passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```
