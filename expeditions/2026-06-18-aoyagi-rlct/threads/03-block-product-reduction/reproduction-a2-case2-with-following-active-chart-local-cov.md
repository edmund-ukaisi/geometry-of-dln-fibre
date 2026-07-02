# A2 Case 2 With-Following Active Chart Local COV

## Purpose

This note records the source-side change-of-variables calculation for the
active selected-entry chart in the enlarged Case 2 coordinates.  This is a
local source-space theorem, not an endpoint-Haar theorem.  Its role is to
separate the elementary selected-entry Jacobian factor from the later problem
of transporting Haar through the endpoint topology-tuple map and the
retained-passive raw-order map.

## Lean Landing

The formal checkpoint is in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointDerivative.lean
```

It adds:

```text
activeSelectedEntryChartMap_injOn_of_subset_pivotNonzero
map_activeSelectedEntryChart_withDensity_sourceDensity_eq_restrict_image_of_subset_pivotNonzero
```

The second theorem is stated for an arbitrary additive Haar source measure
`mu`, a null-measurable patch `Omega`, and the hypothesis that `Omega` lies in
the selected nonzero-pivot locus.

## Calculation

For

```text
z = ((passive fields, y_next), F_follow)
```

set

```text
p = case2PassiveThetaPivotNext n hS hnext,
A(z) = ((passive fields, chartMap p y_next), F_follow).
```

The active chart is the identity on passive fields and on the following
factor.  On the center block it is the selected-entry chart

```text
(chartMap p y)_p = y_p,
(chartMap p y)_i = y_p y_i     for i != p.
```

Putting the pivot coordinate first, the derivative matrix has triangular
shape

```text
[ 1   0  ]
[ *  y_p I ]
```

so

```text
|det D A(z)|
  = |y_next p|^(card(center.erase p))
  = SelectedEntrySignedBox.CenterCoord.sourceDensity p y_next.
```

The passive and following identity factors contribute determinant `1`.  Hence
for any null-measurable source patch `Omega` contained in the nonzero-pivot
locus, mathlib's finite-dimensional Jacobian theorem gives

```text
map A ((mu.restrict Omega).withDensity
  (fun z => ofReal (sourceDensity p z.1.yNext)))
  = mu.restrict (A '' Omega),
```

for any additive Haar source measure `mu`.

## Locality

The nonzero-pivot hypothesis is essential: at `y_p = 0`, the selected-entry
chart collapses all non-pivot center coordinates and is not injective.  This
is why the theorem targets the actual image `A '' Omega` rather than a full
ambient chart.

## Boundary

This proves only the selected-entry source-space COV.  It does not identify
the endpoint image `Y '' Omega` with determinant Haar, does not prove a raw
pushforward, and does not remove the retained-passive raw-order Jacobian
factor.

## Verification

Focused local module build and full local build passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaEndpointDerivative
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`lean/scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` passed, and the touched Lean-file forbidden-marker scan
was clean.  Direct axiom probes for both declarations reported:

```text
[propext, Classical.choice, Quot.sound]
```
