# Statement card - A4 Case 2 source-chart selected-entry microcertificate adapter

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case2DisplayedCenterSqFormalJacobianChartCertificate.sourceChartPoint`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.loss_sourceChartPoint_eq_centerSq`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPrior_sourceChartPoint_eq_det`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.loss_monomial_sourceChartPoint`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPrior_monomial_sourceChartPoint`

## Claim

The displayed continuing Case 2 source chart point can be evaluated inside the
existing selected-entry one-chart finite normal-crossing microcertificate.  At
that point, the microcertificate's chart map is the displayed source chart
map, its loss is the residual-center square-sum, its loss unit is the
normalized square-sum factor, and its Jacobian/prior value is the formal
pivot-first determinant.

## Inputs Kept Explicit

- ordered field coefficient type;
- `1 <= S`;
- continuation hypothesis `J+1 <= prefixMinNat n (S+1)`;
- selected variable `u`;
- source residual function `residual : Nat × Nat -> K`.

## Proved

The source chart point is constructed as the local microcertificate point
`(u, residual|_{E \\ {p}})`.  Lean proves that the microcertificate chart map
at this point is pointwise the displayed Case 2 source chart map.  It also
proves that the loss is the displayed residual-center square-sum, the loss
unit is the normalized square-sum factor, and the Jacobian/prior value agrees
with the formal pivot-first determinant.  The final two lemmas restate the
microcertificate's loss and Jacobian/prior monomial identities at this source
chart point.

## Not Proved

No chart coverage, no source production, no transition regularity, no analytic
unit neighbourhood, no analytic Jacobian or volume-form theorem, no total DLN
loss monomial identity, no global A0 chart family, no active-ratio lower
bound, no chart-count theorem, no pole order, and no RLCT extraction.

## Verification

Independent review passed:

- `review-case2-source-chart-selected-entry-microcertificate-adapter-a4.md`

Controller gates passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```
