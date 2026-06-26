# Statement Card - A2 Retained-Passive Monomial-Unit Local-Measure Handoff

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialUnits
```

## Claim

For the retained-passive p.13 local source, supplied monomial-times-unit
identities and unit bounds on a weighted signed-box source chart imply the
chart-side residual lower bound and source-density bounds consumed by the
retained-passive signed-box local-measure handoff.

## Proved

- the existing monomial-unit package derives source-density measurability,
  residual monomial lower bound, source-density nonnegativity, and
  source-density upper bound;
- these facts feed the retained-passive signed-box local-measure handoff;
- the conclusion is the same local finite p.13 regular-coordinate integral
  over a neighborhood inside the source-rank stratum.

## Assumed

- finite-dimensional fixed-base endpoint data;
- global continuity `Continuous Cedge`;
- the self-base equality for `Cedge x0`;
- `SFinite μ` and additive Haar structure for the regular-coordinate measure;
- regular-side positive radius/lower constant, nonnegative upper density
  constant, and positive `t`;
- the weighted signed-box source-measure pushforward onto the retained-passive
  local source;
- signed-box numeric side conditions: positive residual lower constant,
  nonnegative source-density upper constant, positive box radii, and
  `2 * t * kres i < hres i + 1`;
- source-chart a.e. measurability;
- density-unit a.e. measurability;
- residual and source-density monomial-times-unit identities;
- residual-unit lower bound, density-unit nonnegativity, and density-unit
  upper bound;
- local loss lower bound and density bounds in `nhdsWithin x0` of the
  retained-passive local source.

## Cited

None.  This is Lean plumbing plus the elementary signed-box monomial-unit
inequality package already formalised in
`RegularSuspensionLocalMeasure.lean`.

## Deferred

Construction of the source chart, proof of the pushforward identity, proof of
the monomial-unit identities and unit bounds, Jacobian/density transport,
original-loss comparison, normal crossings, pole order, and RLCT extraction.

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

Status at creation: focused build passed.
