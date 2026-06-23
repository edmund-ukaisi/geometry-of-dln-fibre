# Statement Card - A4 selected-entry multi-chart source-point adapter

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

## Claim

For the finite all-pivot selected-entry chart-family certificate, each chart
index `c` has a source point obtained by delegating to the existing one-pivot
source point for the pivot selected by `chartEquiv c`.

At that source point, the chart map, finite loss, normalized loss unit, formal
pivot-first Jacobian/prior determinant, and the loss/Jacobian monomial
identities agree with the corresponding one-pivot selected-entry source-chart
calculation.

## Lean Names

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartPoint_eq
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartPoint_eq_centerSq
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartPoint_eq
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartPoint_eq_det
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartPoint
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartPoint
```

## Inputs Kept Explicit

- a nonempty finite center `center.Nonempty`;
- a supplied chart-indexing equivalence `Fin center.card ≃ center`;
- a chart index `c`;
- the selected-entry source coordinate `u`;
- an ambient residual assignment `residual : ι → K`;
- ordered-field hypotheses inherited from the one-pivot unit calculation.

## Not Proved

No analytic atlas coverage, no transition regularity between pivot charts, no
analytic Jacobian/volume-form theorem, no source production of successor
matrices or recurrence post-data, no global DLN loss certificate, no global
A0 active-ratio lower bound, no pole-order theorem, and no RLCT theorem.

## Verification

Run:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```
