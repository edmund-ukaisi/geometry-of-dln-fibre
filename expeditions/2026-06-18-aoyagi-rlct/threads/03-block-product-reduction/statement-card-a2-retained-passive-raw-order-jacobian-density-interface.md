# Statement Card - A2 Retained-Passive Raw-Order Jacobian Density Interface

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Lean Names

```text
topologyTupleEdgeRawOrderFDerivAbsDet
topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
eventually_topologyTupleEdgeRawOrderFDerivAbsDet_pos_nhds
exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds_of_continuousAt
exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds_of_continuousAt
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-jacobian-density-interface.md
```

## Claim

Lean packages the forward retained-passive raw-order absolute Jacobian
determinant

```text
|det (fderiv R topologyTupleEdgeRawOrder z)|
```

and proves that it is strictly positive on the retained-passive tuple
determinant chart.  It is eventually positive near any determinant-chart
point.  Under an explicit `ContinuousAt` hypothesis for this absolute
determinant function at the base point, Lean also derives a positive local
lower bound and a positive local upper bound.

## Role

This is the first retained-passive density-facing API after tangent
invertibility.  It is suitable for later finite-integral handoffs that need a
positive continuous density factor, but it intentionally keeps the continuity
of the retained-passive Jacobian density as a supplied hypothesis.

## Nonclaims

No continuity of the retained-passive derivative family, no explicit
determinant formula, no inverse-density formula, no measure pushforward, no
source-density identity, no normal crossing, no pole order, and no RLCT
statement is part of this slice.

## Verification

Review:

```text
review-a2-retained-passive-raw-order-jacobian-density-interface.md
```

accepted by xhigh read-only explorer `Laplace the 4th`.

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
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
