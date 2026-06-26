# Statement Card - A2 retained-passive determinant-chart domain

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.toCoordinateData_passiveA1_units_of_detChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_readbacks_eq_targets_of_detChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_ext_of_detChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.injOn_edgeMatrix_detChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.TopologyTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.topologyTuple
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.isOpen_detChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChartSet_mem_nhds
```

## Reproduction

```text
reproduction-a2-retained-passive-det-chart-domain.md
```

## Claim

Lean now names the determinant-domain predicate for nonredundant
retained-passive coordinates:

```text
det(Ctop) is a unit,
det(A1passive p) is a unit for every p : Fin M.
```

The finite readback and extensionality theorems are repackaged on this domain,
and `injOn_edgeMatrix_detChartSet` proves that the nonredundant source map is
injective on the determinant-domain set.

Lean also gives the coordinate record the product topology on its finite
matrix fields and proves `isOpen_detChartSet`: the determinant-domain set is
open under `[TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]`.

## Method

The finite domain wrappers call the previously proved readback and
extensionality theorems after unpacking `detChart`.

The openness theorem writes the determinant-domain set as the intersection of
the active `Ctop` determinant-unit locus and the finite intersection of the
passive `A1passive` determinant-unit loci.  Each locus is the continuous
preimage of the open unit set under a matrix determinant.

## Role

This is the first named domain/topology layer for the nonredundant
retained-passive chart.  It packages the side conditions that future source
coverage, image, and measure-transport statements must keep explicit.

## Nonclaims

No source-rank coverage, source/image equality, image openness, continuity of
`edgeMatrix`, measure pushforward, density/Jacobian theorem, normal crossings,
pole order, or RLCT extraction is proved.

The object still stores `Ctop` directly; it does not introduce the centered
active coordinate `X=Ctop-I`.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

This focused check passed on 2026-06-26.

Full-library and hygiene checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

The focused check was independently rerun by xhigh reviewer
`Poincare the 3rd` and passed.  Review:
`review-a2-retained-passive-det-chart-domain.md`.
