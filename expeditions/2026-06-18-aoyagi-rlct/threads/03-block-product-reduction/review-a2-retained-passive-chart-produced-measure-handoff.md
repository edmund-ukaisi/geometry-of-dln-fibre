# Review - A2 retained-passive chart-produced measure handoff

Date: 2026-06-26.

Reviewer: controller pre-review plus independent xhigh reviewer `Gauss the 4th`.

## Scope

Audit the new chart-produced-measure handoff in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean` and its claim
boundary.

Reviewed Lean artifacts:

```text
measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix_chartProducedMeasure
```

## Verdict

PASS.  No blocking findings.

The checkpoint is a narrow chart-produced-measure handoff.  It is not a proof
of original source-measure transport.

## Checks

The support lemma is standard measure theory.  It uses measurability of the
retained-passive local source, `ae_map_iff`, and
`Measure.restrict_eq_self_of_ae_mem`.

The selected-entry chart-produced theorem defines the source measure as the
signed box with the selected-entry source density, defines `mu` as its image
under `sourceChart`, and derives the old `hmap` internally.  It still requires
the chart image to lie in the retained-passive local source and still requires
the local loss/density bounds.

The source-readback variant derives the selected-entry residual square-sum
from the existing source-readback residual-factor matrix theorem before
calling the chart-produced selected-entry handoff.

No source-boundary overclaim is present in the Lean docstrings or statement
card: original-prior transport, source-rank coverage, Jacobian/prior
compatibility, normal crossings, pole order, and RLCT extraction remain
outside the claim.

The independent reviewer also found no formalisation or mathematical
correctness issue.  Their main check was that the support lemma proves only
restriction equality for an already pushed-forward measure, that the
selected-entry chart-produced theorem defines `mu` as this pushforward in the
statement itself, and that the source-readback variant is only a wrapper that
first derives the residual square-sum equality.

## Verification

Controller check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

The focused build passed on 2026-06-26, with the existing warning stream from
`ProductReductionStepRegularDensity`.

The independent reviewer also checked:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```
