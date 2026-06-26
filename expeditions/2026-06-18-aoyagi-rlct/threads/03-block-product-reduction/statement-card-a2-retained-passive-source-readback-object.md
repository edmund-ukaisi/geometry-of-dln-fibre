# Statement Card - A2 retained-passive source-readback object

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackTransformedEdge
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_edgeMatrix_eq
```

## Reproduction

```text
reproduction-a2-retained-passive-source-readback-object.md
```

## Claim

There is an explicit total source-side readback map from an arbitrary
retained-passive-shaped edge family to nonredundant retained-passive coordinate
data.  On the determinant-chart image of the retained-passive source map, this
readback map recovers the original coordinate data:

```text
sourceReadback data.edgeMatrix = data.
```

## Method

The readback object uses the deterministic suffix state `S_i(E)` and
transformed edge `T_p(E)`.  Its fields are:

```text
A1passive p = topLeftCorner T_{p.succ}(E)
F2 p        = -((topLeftCorner T_p(E))^-1 * upperRightBlock T_p(E))
A3passive p = lowerLeftBlock T_{p.castSucc}(E)
C p         = schurResidualBlock T_p(E)
Ctop        = S_0(E).Ctop
F3          = lowerLeftBlock S_0(E).L.
```

The inverse-on-image proof applies the existing determinant-chart readback
theorem and then compares the six structure fields.

## Role

This packages the finite inverse formulas into a reusable map.  It is the
right input for later continuity/local-inverse work, because downstream
statements can refer to one readback object rather than re-unfolding every
coordinate projection.

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

The focused coordinate-file check was independently rerun by xhigh reviewer
`Averroes the 3rd` and passed.  Review:
`review-a2-retained-passive-source-readback-object.md`.
