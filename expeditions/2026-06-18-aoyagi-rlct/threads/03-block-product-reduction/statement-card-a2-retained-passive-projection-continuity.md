# Statement Card - A2 retained-passive projection continuity

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_A1passive
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_F2
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_A3passive
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_C
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_Ctop
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_F3
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_A1seed
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_F2full
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_A3seed
```

## Reproduction

```text
reproduction-a2-retained-passive-projection-continuity.md
```

## Claim

Every stored finite matrix field of the nonredundant retained-passive
coordinate object is continuous for the product topology on
`(A1passive,F2,A3passive,C,Ctop,F3)`.

The component maps of the dummy-slot embeddings `A1seed`, `F2full`, and
`A3seed` are also continuous: each component is either a stored-field
projection or a constant zero map.

## Method

The stored-field theorems compose `continuous_topologyTuple` with product
projections and finite-family evaluation maps.

The dummy-extension theorems split by `Fin.cases` or `Fin.lastCases`, reducing
each branch to either an existing projection-continuity theorem or
`continuous_const`.

## Role

This is a staging layer between domain openness and endpoint/source-map
continuity.  It exposes the product-topology coordinates that later proofs of
`solvedA1`, `solvedA3`, and `edgeMatrix` continuity will compose.

## Nonclaims

No continuity of `solvedA1`, `solvedA3`, `toCoordinateData`, or `edgeMatrix`
is proved.  No image openness, source-rank coverage, source/image equality,
measure transport, density/Jacobian theorem, normal crossings, pole order, or
RLCT extraction is proved.

## Verification

Focused check passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

Full-library and hygiene checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

The focused check was independently rerun by xhigh reviewer
`Parfit the 3rd` and passed.  Review:
`review-a2-retained-passive-projection-continuity.md`.
