# Statement Card - A2 retained-passive selected-entry source-stratum bounds

Date: 2026-06-29.

## Claim

The retained-passive selected-entry signed-box finite-integral handoff can use
loss and density bounds stated on the source-rank stratum, while retaining the
selected-entry residual chart and local-source pushforward hypotheses.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Declaration:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds
```

## Inputs Kept Explicit

- selected-entry signed-box source chart measurability;
- pushforward identity for `mu.restrict retainedPassiveP13LocalSource`;
- selected-entry residual square-sum readout;
- positive selected-entry radii and critical inequality;
- source-stratum loss lower bound;
- source-stratum density nonnegativity and upper bound.

## Nonclaims

No selected-entry chart image equality, no source-rank coverage theorem, no
external/original source-prior transport, no Jacobian comparison, no analytic
atlas, no normal crossings, no pole order, and no RLCT statement is proved.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

xhigh review passed:
`review-a2-retained-passive-selected-entry-source-stratum-bounds.md`.

Final standard checks passed:

```text
cd lean
scripts/sorries

git diff --check
rg -n "\bsorry\b|#exit|native_decide|\baxiom\b" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```
