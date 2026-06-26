# Statement Card - A2 retained-passive nonredundant coordinate data

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.A1seed
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.F2full
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.A3seed
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.toCoordinateData
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.toCoordinateData_passiveA1_units
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_readbacks_eq_targets
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_ext
```

## Reproduction

```text
reproduction-a2-retained-passive-nonredundant-coordinate-data.md
```

## Claim

Lean now defines a nonredundant retained-passive finite coordinate object whose
fields are exactly:

```text
A1passive : Fin M -> Matrix rho rho K
F2        : for non-final F2 indices p.castSucc
A3passive: Fin M -> lower-left passive matrices
C         : all residual blocks
Ctop
F3.
```

It embeds this object into the earlier `RetainedPassiveCoordinateData` by
filling the dummy slots canonically:

```text
A1seed_0 = 0,
A3seed_last = 0,
F2_last = 0.
```

The theorem `edgeMatrix_readbacks_eq_targets` proves readbacks for every stored
field under passive `A1passive` determinant-unit hypotheses and `det(Ctop)`
unit.  The theorem `edgeMatrix_ext` proves full equality of nonredundant
coordinate data from equality of their edge families under the same unit side
conditions on both data objects.

## Method

The proof embeds the nonredundant object into the older bundled coordinate
data and calls the previously proved recoverable-field theorems.  The passive
`A1` unit side condition is converted to the old seed-family side condition by
splitting `Fin (M+1)` into `0` and successor cases.  Full extensionality is
valid here because the dummy fields have been removed.

## Role

This is a sharper finite coordinate API for the retained-passive source map.
It upgrades the previous recoverable-field extensionality theorem into full
injectivity for the actual stored coordinate object.

## Nonclaims

No open coordinate domain, topology, source-rank coverage, source/image
equality, measure pushforward, density/Jacobian theorem, normal crossings,
pole order, or RLCT extraction is proved.

The object stores `Ctop` directly; it does not yet introduce the centered
active coordinate `X=Ctop-I`.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

This focused check passed on 2026-06-26.

Full-library and hygiene checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

The focused check was independently rerun by xhigh reviewer `Locke the 3rd`
and passed.  Review:
`review-a2-retained-passive-nonredundant-coordinate-data.md`.
