# Statement Card - A2 retained-passive source-recursive chart homeomorphism

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.solvedA1_det_isUnit_of_detChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_edgeMatrix_of_detChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_sourceRecursiveDetChart_subtype
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_sourceReadback_detChart_subtype
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChart_sourceRecursiveDetChart_homeomorph
```

## Reproduction

```text
reproduction-a2-retained-passive-source-recursive-chart-homeomorph.md
```

## Claim

The retained-passive nonredundant determinant chart is homeomorphic to the
explicit source-recursive determinant edge chart:

```text
{data // data.detChart} equiv_homeomorph {E // sourceRecursiveDetChart E}.
```

The forward map is `data.edgeMatrix`; the inverse map is `sourceReadback E`.

## Method

First prove that `data.edgeMatrix` satisfies `sourceRecursiveDetChart` whenever
`data.detChart`.  The transformed-edge top-left readback is the solved full
`A1` block, and all solved full `A1` blocks have unit determinant on
`data.detChart`.

Then wrap the already proved ambient continuity theorems into subtype-valued
maps.  The left and right inverse laws are exactly the previously banked
finite inverse theorems:

```text
sourceReadback_edgeMatrix_eq
edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart.
```

## Role

This packages the retained-passive chart as a genuine topological coordinate
equivalence on the explicit source-recursive determinant domain.  It is the
natural bridge after the finite two-sided inverse algebra.

## Nonclaims

No ambient openness of `sourceRecursiveDetChart`, equality with the whole
source image, global source/image theorem, source-rank coverage, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
extraction is proved.

## Verification

Focused and full checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

The full build emitted only pre-existing linter warnings from unrelated
Core/downstream files.

Review:
`review-a2-retained-passive-source-recursive-chart-homeomorph.md`.
