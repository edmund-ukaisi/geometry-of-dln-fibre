# Statement Card - A2 retained-passive solved-A3 continuity

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveA3WithoutLast
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_residualFactorProduct_C
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.solvedA1_det_isUnit_of_detChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_residualFactorProduct_solvedA1_detChart_subtype
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.residualFactorProduct_solvedA1_det_isUnit_of_detChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_solvedA3_detChart_subtype
```

## Reproduction

```text
reproduction-a2-retained-passive-solved-a3-continuity.md
```

## Claim

On the nonredundant determinant-chart subtype, every component of the solved
full lower-left family is continuous:

```text
data ↦ (data.1.toCoordinateData).solvedA3 p.
```

The proof also records the finite-tail continuity and determinant-unit
support lemmas needed by the final component.

## Method

The non-final solved `A3` components reduce to `A3seed`.

The final component is

```text
-(F3 - earlyTail) * CtopLast.
```

The early tail is a finite decreasing sum.  Each summand is continuous from
stored `C` product continuity, zeroed-`A3seed` continuity, solved-`A1` product
continuity, inverse continuity on solved-`A1` determinant-unit products, and
matrix algebra continuity.

## Role

This completes the endpoint-family continuity layer after the solved-`A1`
rung.  The next topology target is the nonredundant retained-passive
`edgeMatrix` source map on the determinant-chart subtype.

## Nonclaims

No continuity of `edgeMatrix` is proved.  No image openness, source-rank
coverage, source/image equality, measure transport, density/Jacobian theorem,
normal crossings, pole order, or RLCT extraction is proved.

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
`Sartre the 3rd` and passed.  Review:
`review-a2-retained-passive-solved-a3-continuity.md`.
