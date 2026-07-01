# Reproduction - A2 p.13 Source-Set Measure Bridge

Date: 2026-07-01.

Status: pen-and-paper check before Lean.  This specializes the edge-family
restricted measure bridge to the public p.13 fixed-base retained-passive
source chart and its named source edge-family set.

## Question

Let

```text
sourceChart :=
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U0 hU0
```

and let

```text
sourceSet :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U0 hU0.
```

Can the generic raw-order-to-edge-family restricted measure comparison be
rewritten with this named p.13 chart and named source set?

## Calculation

The generic edge-family bridge uses

```text
psi y := tupleToEdgeFamily b (rawOrderMatrixTuple e y),
```

where `b` is the p.13 fixed endpoint basis family and `e` is the canonical
finite reindexing.  On the raw source-recursive determinant chart, the p.13
coordinate bridge proves

```text
edgeFamilyMatrixTuple b (sourceChart y) = rawOrderMatrixTuple e y.
```

Because `tupleToEdgeFamily b` is the inverse of `edgeFamilyMatrixTuple b`,
this gives the pointwise chart-domain equality

```text
sourceChart y = psi y
```

for `y` in the raw source set.  This equality is not global; it is used only
under `m.restrict rawSourceSet`.

Therefore

```text
Measure.map sourceChart (m.restrict rawSourceSet)
  = Measure.map psi (m.restrict rawSourceSet)
```

by `Measure.map_congr` and the a.e. fact that a restricted measure lives on
its restricting set.  The existing source-image theorem gives

```text
sourceChart '' rawSourceSet = sourceSet.
```

Together with the generic edge-family bridge,

```text
Measure.map psi (m.restrict rawSourceSet)
  = c • (originalEdgeFamilyVolume b).restrict (psi '' rawSourceSet),
```

we obtain

```text
Measure.map sourceChart (m.restrict rawSourceSet)
  = c • (originalEdgeFamilyVolume b).restrict sourceSet,
```

where

```text
c :=
  (Measure.map (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W B U0) m)
    .addHaarScalarFactor (originalTupleVolume d).
```

For the formal-product Jacobian measure, the existing retained-passive local
Jacobian theorem already gives

```text
Measure.map (fun z => sourceChart (topologyTupleEdgeRawOrder z))
  ((m.restrict detChart).withDensity formalProductAbsDet)
= (Measure.map sourceChart (m.restrict rawSourceSet)).restrict sourceSet.
```

The existing support theorem says the restriction on the right is the same
measure.  Applying the restricted source-set comparison above gives the final
scalar-restricted original edge-family volume.

### Chart-piece restriction corollary

Let `chartPiece` be a measurable subset of `sourceSet`.  If

```text
muP13
  = c • (originalEdgeFamilyVolume b).restrict sourceSet,
```

where `muP13` is either the unweighted p.13 raw-order pushforward or the
formal-product Jacobian pushforward, then restricting both sides to
`chartPiece` gives

```text
muP13.restrict chartPiece
  = (c • (originalEdgeFamilyVolume b).restrict sourceSet).restrict chartPiece.
```

Scalar restriction commutes with restriction, so the right side is

```text
c • ((originalEdgeFamilyVolume b).restrict sourceSet).restrict chartPiece.
```

The containment `chartPiece ⊆ sourceSet` then collapses the double restriction:

```text
((originalEdgeFamilyVolume b).restrict sourceSet).restrict chartPiece
  = (originalEdgeFamilyVolume b).restrict chartPiece.
```

Hence the chart-piece equality is

```text
muP13.restrict chartPiece
  = c • (originalEdgeFamilyVolume b).restrict chartPiece.
```

This corollary does not identify `chartPiece` with any passive-theta source
image.  It is only a restriction of the already-proved p.13 source-set
comparison to a supplied measurable subset of the named source set.

## Lean Target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

with:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_tupleToEdgeFamily_rawOrderMatrixTuple
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_chartPiece_eq_smul_originalEdgeFamilyVolume_restrict_chartPiece
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_smul_originalEdgeFamilyVolume_restrict_chartPiece
```

## Kill Conditions

- If the pointwise equality is used outside the raw source chart, the theorem
  overclaims.
- If `sourceSet` is replaced by a rank stratum or global original source
  without a separate coverage theorem, the theorem overclaims.
- If the scalar is identified with `1`, the theorem overclaims.
- If the theorem is cited as restricted Haar, normal crossings, pole order,
  or RLCT extraction, it overclaims.
- If the chart-piece corollary is used with a set only known to lie in a
  passive-theta local source, but not in the named p.13 source edge-family set,
  it overclaims.

## Nonclaims

No theorem here proves source-rank coverage, full source-image coverage,
restricted Haar structure, exact scalar normalization, normal crossings,
pole order, or RLCT extraction.
