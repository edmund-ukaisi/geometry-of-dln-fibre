# Statement Card - A2 retained-passive chart-produced measure handoff

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

## Lean Names

```text
measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix_chartProducedMeasure
```

## Reproduction

```text
reproduction-a2-retained-passive-chart-produced-measure-handoff.md
```

## Claim

If a selected-entry signed-box source measure is pushed forward by a chart
`sourceChart`, and the chart lands in the retained-passive p.13 local source,
then the retained-passive selected-entry local-measure handoff can be applied
without an explicit `hmap` hypothesis.

The final source-readback variant combines this chart-produced measure handoff
with the existing residual-factor matrix readout, so the residual square-sum
hypothesis is also derived from the supplied source-readback factor identity.

## Method

The support lemma proves

```text
(Measure.map sourceChart eta).restrict localSource
  = Measure.map sourceChart eta
```

from a.e. measurability of `sourceChart`, measurability of `localSource`, and
a.e. membership of `sourceChart y` in `localSource`.

For the selected-entry source measure, a.e. measurability transfers from the
product signed box to the with-density measure by absolute continuity.  The
resulting support equality supplies the old `hmap` field internally.

## Nonclaims

This is not a source-measure construction for an external prior.  It does not
identify the original DLN source measure, prove source-rank coverage, compute
or transport a Jacobian for an original coordinate change, prove density/prior
compatibility, establish normal crossings, compute pole order, or extract an
RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

Passed on 2026-06-26, with the existing repository warning stream from
`ProductReductionStepRegularDensity`.

Review:

```text
review-a2-retained-passive-chart-produced-measure-handoff.md
```
