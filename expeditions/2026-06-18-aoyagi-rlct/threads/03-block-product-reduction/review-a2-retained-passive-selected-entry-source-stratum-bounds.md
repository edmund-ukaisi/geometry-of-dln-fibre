# Review - A2 retained-passive selected-entry source-stratum bounds

Date: 2026-06-29.

Reviewer: xhigh `Aristotle the 2nd`.

Status: PASS.

## Findings

No findings.

## Checks

The reviewer checked the theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds
```

in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

The review confirmed:

- the pushforward hypothesis `hmap` remains explicit;
- the selected-entry residual readout remains explicit;
- the only API shift is that `hloss`, `hdensity_nonneg`, and `hdensity_le`
  are stated on the source-rank stratum;
- residual positivity and residual negative-power integrability are derived
  only on the retained-passive local source from the selected-entry chart data;
- the source-rank restricted integral is delegated to the boundary-explicit
  source-stratum/local-source bridge through the retained-passive local-source
  inclusion.

The reviewer did not see any assertion of selected-entry image equality,
source-rank coverage, external/original source-prior transport, Jacobian
comparison, normal crossings, pole order, or RLCT.

## Verification

The reviewer ran:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

and it passed.
