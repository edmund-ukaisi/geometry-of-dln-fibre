# Statement Card - Theorem 2 rank-width regular-shift bridge

## Lean targets

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_regularVariableCountShift`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_regularVariableCountShift`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/Theorem2RankWidthRegularShiftBridge.lean`
- Reproduction:
  `threads/06-dln-translation/reproduction-theorem2-rank-width-regular-shift-bridge-a6.md`

## Claim

Definition 3 source data plus source-range rank-width hypotheses produce the
selected-width family and ceiling datum for the final socket.  If the reduced
finite minimum plus Aoyagi's regular term equals the displayed Theorem 2
lambda formula, and the reduced finite order equals the displayed order
formula, then the shifted exponent datum or shifted chart certificate fills
the supplied final boundary.

## Scope

The shifted A0 extraction hypothesis remains supplied.  The reduced
minimum/order obligations remain supplied.  This is final-socket composition
and finite exponent-array arithmetic; it does not construct regular-suspension
charts, analytic ideal transport, normal-crossing charts, active-ratio bounds,
chart counts, pole order, or RLCT.

## Verification

Focused Lean check and module build passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Theorem2RankWidthRegularShiftBridge.lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Theorem2RankWidthRegularShiftBridge
```

The source-rank wrapper also checks/builds after delegating to this bridge:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Theorem2SourceRankRegularShiftBridge.lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Theorem2SourceRankRegularShiftBridge
```

Review:
`threads/06-dln-translation/review-theorem2-rank-width-regular-shift-bridge-a6.md`.
