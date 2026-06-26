# Statement Card - A2 retained-passive open partial homeomorphism

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChartSet_sourceRecursiveDetChartSet_homeomorph
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChart_sourceRecursiveDetChart_openPartialHomeomorph
```

## Reproduction

```text
reproduction-a2-retained-passive-open-partial-homeomorph.md
```

## Claim

The retained-passive determinant coordinate chart and the explicit
source-recursive determinant edge chart form an ambient
`OpenPartialHomeomorph`.

## Method

Rewrite the previously proved subtype homeomorphism from predicate subtypes to
the named set subtypes.  Then build the ambient open partial homeomorphism
with source `detChartSet`, target `sourceRecursiveDetChartSet`, forward map
`edgeMatrix`, and inverse map `sourceReadback`.  The inverse laws and mapping
properties are exactly the existing finite inverse theorems, and openness is
the pair of already-proved domain-openness theorems.

## Role

This gives later chart and local-measure work a single explicit local chart
object.  It is the correct topological package after the finite inverse,
subtype homeomorphism, and source-recursive openness rungs.

## Nonclaims

No equality with the whole source image, source-rank coverage, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
extraction is proved.

## Verification

Focused check passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

Full and hygiene checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```
