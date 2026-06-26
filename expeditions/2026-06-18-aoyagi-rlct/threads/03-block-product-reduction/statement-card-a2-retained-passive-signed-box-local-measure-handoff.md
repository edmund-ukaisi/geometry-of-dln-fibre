# Statement Card - A2 Retained-Passive Signed-Box Local-Measure Handoff

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialLower
```

## Claim

For the retained-passive p.13 local source, a supplied weighted signed-box
source-measure pushforward and supplied monomial residual/density bounds imply
the residual positivity/integrability hypotheses needed by the retained-
passive local-measure handoff.  Therefore the finite p.13 regular-coordinate
integral holds locally over the source-rank stratum.

## Proved

- global `Continuous Cedge` gives measurable fixed-base edge matrices;
- the existing weighted signed-box residual-source constructor applies to
  `paperEndpointFixedBaseRetainedPassiveP13LocalSource`;
- the resulting residual hypotheses feed the retained-passive local-measure
  handoff.

## Assumed

- finite-dimensional fixed-base endpoint data;
- global continuity `Continuous Cedge`;
- the self-base equality for `Cedge x0`;
- `SFinite μ` and additive Haar structure for the regular-coordinate measure;
- regular-side positive radius/lower constant, nonnegative upper density
  constant, and positive `t`;
- the weighted signed-box source-measure pushforward onto the retained-passive
  local source;
- chart-side source-density measurability, chart measurability, monomial
  residual lower bound, source-density nonnegativity, and source-density upper
  bound;
- signed-box numeric side conditions: positive residual lower constant,
  nonnegative residual density constant, positive box radii, and
  `2 * t * kres i < hres i + 1`;
- local loss lower bound and density bounds in `nhdsWithin x0` of the
  retained-passive local source.

## Cited

None.  This is Lean plumbing between already formalised retained-passive and
signed-box local-measure infrastructure.

## Deferred

Construction of the source chart, proof of the pushforward identity,
Jacobian/density transport, original-loss comparison, normal crossings, pole
order, and RLCT extraction.

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

Status at creation: focused build passed.
