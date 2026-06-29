# Review: A2 retained-passive small-box chart-produced residual bound

Reviewer: xhigh `Carson the 2nd`

Additional reviewer: xhigh `Huygens the 3rd`

Verdict: PASS.

## Checked Theorems

```text
residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_of_residual_eq_of_smallBox
residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density_of_smallBox
```

## Findings

No findings.

The review confirmed that the theorems use only the chart-produced measure
`mu := Measure.map sourceChart sourceMeasure`, instantiate the source-side
small-box residual bound at `Rreg` rather than `Rmax`, and pass only the
resulting retained-passive local-source residual bound into the existing
fixed-radius theorem.

The small-box hypotheses match the selected-entry source lemma exactly.

Huygens the 3rd reviewed the continuous-density small-box wrapper and returned
PASS.  The review accepted the radius discipline: `R` is produced by the
continuous-density theorem before `delta` is quantified, so the small-box
inequality is required at `R^2` and not inferred from `Rmax^2`.  The theorem
continues to use the selected-entry chart-produced source measure and does not
claim source/image equality or external-prior transport.

## Reviewer Note

The reviewer also typechecked
`DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean` from the Lean package
directory.
