# Statement Card - A2 retained-passive raw edge tuple target

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.EdgeFamilyTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rawEdgeTupleA1
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rawEdgeTupleA3
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeFamilyOfRawOrderTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeFamilyRawOrderTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeFamilyRawOrderTuple_edgeFamilyOfRawOrderTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeFamilyOfRawOrderTuple_edgeFamilyRawOrderTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeFamilyRawOrderLinearEquiv
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.topologyTupleEdgeRawOrder
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.injOn_topologyTupleEdgeRawOrder_detChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-edge-tuple-target.md
```

## Claim

An edge family with edge shapes

```text
E p : Matrix (rho Sum kappa p.succ) (rho Sum kappa p.castSucc) R
```

is linearly equivalent to the existing retained-passive `TopologyTuple`
product order by raw block extraction:

```text
edge 0 top-left      -> Ctop
edges 1..M top-left  -> A1passive
all upper-right      -> F2
edges 0..M-1 lower-left -> A3passive
last lower-left      -> F3
all lower-right      -> C
```

Composing this raw readout with `topologyTupleEdgeMatrix` gives an endomap
`topologyTupleEdgeRawOrder` on the tuple coordinate space.  The endomap is
injective on `topologyTupleDetChartSet`.

## Method

The raw readout is inverted by `Matrix.fromBlocks`, using `Fin.cases` for the
top-left endpoint split and `Fin.snoc` for the lower-left endpoint split.
The two inverse identities are block identities, ultimately using
`Matrix.fromBlocks_toBlocks` and the endpoint simp rules for `Fin.cases` and
`Fin.snoc`.

Injectivity of `topologyTupleEdgeRawOrder` is obtained by applying
`edgeFamilyOfRawOrderTuple` to an equality of raw tuples, then reducing to
the already-proved `injOn_topologyTupleEdgeMatrix_detChartSet`.

## Role

This supplies the target-coordinate endomap needed before a future
retained-passive derivative/Jacobian theorem.  It turns the edge-family
codomain into the same finite product type as the source tuple without
changing the mathematical map being studied.

## Nonclaims

This is not a retained-passive coordinate inverse for arbitrary edge families.
No derivative, determinant formula, density, measure pushforward, image
equality, homeomorphism, source-rank coverage, source-measure theorem,
normal crossings, pole order, or RLCT extraction is proved.

## Verification

Focused check passed before this card was written:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```
