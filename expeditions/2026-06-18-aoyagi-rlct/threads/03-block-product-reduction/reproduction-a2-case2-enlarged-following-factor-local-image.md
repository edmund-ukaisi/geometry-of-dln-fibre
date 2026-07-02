# Reproduction - A2 Case 2 enlarged following-factor local image

Date: 2026-07-02.

Status: local readback-left-inverse and source-chart image measurability for
the enlarged following-factor source; no measure transport or Jacobian claim.

## Pen-and-Paper Check

For an enlarged coordinate

```text
z = (theta, F)
```

the fixed-base p.13 source chart is obtained by applying the retained-passive
source chart to the endpoint-transported enlarged retained datum.  On the
retained determinant-chart locus, the fixed-base source edge matrix of this
chart has edge matrix equal to the retained datum, so the standard
retained-passive source readback returns that retained datum.

The local domain is the intersection of:

- the preimage of the retained-passive determinant-chart set under the
  enlarged endpoint topology tuple;
- the nonzero selected-pivot condition on `theta.yNext`.

Both conditions are open.  On this domain, the pointwise readback from the
previous slice applies.  The selected-entry field is recovered from raw `C(1)`,
not from the old product `C(1) * C(0)`, and the following factor is recovered
from raw `C(0)`.

For the local source-image theorem, shrink further inside any prescribed open
neighborhood `G`.  The readback-left-inverse gives injectivity of the source
chart on the shrunken open set.  Continuity on that set follows by factoring
the chart through the determinant-chart subtype of retained-passive data.  The
usual Polish/Borel/Lusin-Souslin hypotheses then give measurability of the
local image `sourceChart '' V`.

## Lean Slice

The local readback theorem is in

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
```

with name

```text
exists_open_case2PassiveThetaWithFollowingFactorEndpointSourceChart_readback_leftInverse
```

The local image theorem is in

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
```

with name

```text
exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse
```

## Nonclaims

No source-rank coverage, global source-image equality, measure pushforward,
Jacobian density, determinant-chart Haar transport, finite-integral transfer,
normal-crossing statement, pole order, or RLCT extraction is proved here.
