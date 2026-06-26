# Statement Card - A2 retained-passive source-readback continuity

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuousAt_sourceReadbackSuffixState_fields
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuousAt_sourceReadbackTransformedEdge
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuousAt_sourceReadback
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_sourceReadback_sourceRecursiveDetChart_subtype
```

## Reproduction

```text
reproduction-a2-retained-passive-source-readback-continuity.md
```

## Claim

For arbitrary retained-passive-shaped edge families, the explicit source
readback map is continuous at every base edge family satisfying the recursive
determinant-chart predicate.  Equivalently, it is continuous on the subtype of
edge families satisfying that predicate.

## Method

The recursive determinant predicate requires every transformed edge visited by
the deterministic suffix-state readback to have an invertible selected top-left
corner.  The existing suffix-state topology theorem gives continuity of the
suffix fields.  This yields continuity of every transformed edge, then
continuity of the six readback fields:

```text
A1passive, F2, A3passive, C, Ctop, F3.
```

The `F2` field is the only place where inverse continuity is used.  The final
record-level theorem is assembled through the induced six-field product
topology on nonredundant retained-passive coordinates.

## Role

This is the inverse-side topology companion to the already-landed source-map
continuity and left-inverse theorem.  It prepares a later local inverse or
local-homeomorphism statement, but does not itself prove such a statement.

## Nonclaims

No image membership theorem for arbitrary edge families is proved.  No image
openness, local homeomorphism, source-rank coverage, source/image equality,
measure pushforward, density/Jacobian theorem, normal crossings, pole order,
or RLCT extraction is proved.

## Verification

Focused checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

Full-library and hygiene checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

The focused topology check was independently rerun by xhigh reviewer
`Beauvoir the 3rd` and passed.  Review:
`review-a2-retained-passive-source-readback-continuity.md`.
