# Statement Card - A2 retained-passive source-recursive chart openness

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.mem_sourceRecursiveDetChartSet
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_iff
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet_mem_nhds
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.isOpen_sourceRecursiveDetChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-source-recursive-chart-openness.md
```

## Claim

The explicit source-recursive determinant chart set is open in the ambient
edge-family space.

## Method

Use proof irrelevance to rewrite `sourceRecursiveDetChart` as a finite family
of determinant conditions on the canonical transformed edges.  At a chart
point, the transformed-edge map is continuous for each edge, and the selected
determinant chart is open in matrix space.  Intersect the finitely many
resulting neighborhoods.

## Role

This upgrades the subtype homeomorphism from the previous rung with an ambient
open-source-domain theorem.  It gives the correct local-chart topology for the
explicit retained-passive source-recursive chart.

## Nonclaims

No equality with the whole source image, source-rank coverage, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
extraction is proved.

## Verification

Focused checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

Full and hygiene checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

Review:
`review-a2-retained-passive-source-recursive-chart-openness.md`.
