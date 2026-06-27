# Statement Card - A2 Retained-Passive Raw-Order Weighted Change of Variables

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
lean/DLNFibre.lean
```

## Lean Names

```text
nullMeasurableSet_topologyTupleDetChartSet
map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det
map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det'
map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart'
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-weighted-cov.md
```

## Claim

Lean specializes Mathlib's finite-dimensional real Jacobian theorem to the
retained-passive raw-order tuple chart.  On the retained-passive tuple
determinant chart, pushing forward additive Haar measure weighted by the
forward absolute `fderiv` determinant gives additive Haar measure restricted
to the image.  Using the retained-passive image theorem, the target is also
rewritten as the raw-order source-recursive determinant chart.

## Role

This is the first retained-passive raw-order measure-transport theorem.  It
instantiates the forward weighted change-of-variables identity for the
raw-order chart, but only with the source-side `|det Df|` weight.

## Nonclaims

No explicit determinant formula, no determinant-density continuity, no local
bounded-density estimate, no inverse Jacobian density, no source-prior density
identity, no original DLN source pushforward, no normal crossing, no pole
order, and no RLCT statement is part of this slice.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesMeasure
```

Full build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

Forbidden-marker scan passed:

```text
cd lean
scripts/sorries
```

with `0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.

Whitespace check passed:

```text
git diff --check
```

Review:

```text
review-a2-retained-passive-raw-order-weighted-cov.md
```

accepted by xhigh read-only explorer `Aristotle the 4th`.
