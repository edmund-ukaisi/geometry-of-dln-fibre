# Statement Card - A4 selected-entry multi-chart certificate

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

## Claim

For a nonempty finite selected-entry center `E`, and a supplied chart indexing
equivalence `Fin E.card ≃ E`, there is a finite chart-family
`AoyagiNormalCrossingChartCertificate` whose chart indexed by `c` is the
one-pivot selected-entry chart at the pivot selected by `c`.

Each chart has one active monomial coordinate, loss exponent `1`, formal
Jacobian/prior exponent `|E|-1`, ratio `|E|/2`, chartwise count `1`, and the
whole finite family has exponent minimum `|E|/2` and finite exponent order `1`.

## Lean Names

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.lossExp_chart_zero
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPriorExp_chart_zero
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentMinimum_eq_centerCard_div_two
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_minCountInChart_eq_one
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentOrder_eq_one
```

## Inputs Kept Explicit

- a nonempty finite center `center.Nonempty`;
- a supplied chart-indexing equivalence `Fin center.card ≃ center`;
- ordered-field hypotheses used by the selected-entry unit proof.

## Not Proved

No global DLN normal-crossing certificate, no analytic atlas coverage, no
transition regularity, no analytic Jacobian/volume-form theorem, no source
production of successor matrices or recurrence post-data, no global
active-ratio lower bound, no pole-order theorem, and no RLCT theorem.

## Verification

Run:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb
lean/scripts/sorries
git diff --check
```
