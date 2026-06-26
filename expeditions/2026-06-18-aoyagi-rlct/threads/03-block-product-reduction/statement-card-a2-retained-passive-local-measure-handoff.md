# Statement Card - A2 Retained-Passive Local-Measure Handoff

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
```

## Claim

For the retained-passive p.13 determinant-chart local source, global
continuity of `Cedge` and the self-base hypothesis supply the local coverage
and measurability inputs to the existing local-source finite-integral
consumer.  The conclusion is a finite p.13 regular-coordinate integral over a
shrunk open neighborhood inside the source-rank stratum.

Here

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource
```

is the fixed-base edge-matrix preimage of `sourceRecursiveDetChartSet`; it is
not the source-rank stratum itself.  The local-measure consumer's edge count
parameter is instantiated as `N = M + 1`, matching retained-passive vertices
`Fin (M + 2)` and edges `Fin (M + 1)`.

## Proved

- local source coverage is obtained from
  `exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase`;
- local source measurability is obtained from
  `measurableSet_paperEndpointFixedBaseRetainedPassiveP13LocalSource_of_continuous`;
- the resulting finite-integral statement is obtained by applying
  `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource`.

## Assumed

- finite-dimensional fixed-base endpoint data;
- global continuity `Continuous Cedge`;
- the self-base equality for `Cedge x0`;
- `SFinite μ` and additive Haar structure for the regular-coordinate measure;
- residual positivity and negative-power integrability on the retained-passive
  local source;
- local loss lower bound and density bounds in `nhdsWithin x0` of the
  retained-passive local source.

## Cited

None.  This is Lean plumbing between already formalised local-source and
local-measure theorems.

## Deferred

Source-measure pushforward, Jacobian/density transport, residual
integrability, loss/density estimates from an original DLN loss and prior,
normal crossings, pole order, and RLCT extraction.  In particular, no source
image equality, raw-Haar pushforward, transported prior identity, Jacobian
determinant control, or original-loss comparison is proved here.

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

Status at creation: focused build passed.
