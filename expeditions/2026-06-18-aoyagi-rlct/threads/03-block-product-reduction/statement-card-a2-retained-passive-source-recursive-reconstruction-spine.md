# Statement Card - A2 retained-passive source-recursive reconstruction spine

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.fromBlocks_schurReadbacks_eq
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_Ctop_det_isUnit_of_sourceRecursiveDetChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_detChart_of_sourceRecursiveDetChart
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_F2full_eq_neg_sourceReadbackSuffixState_B
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_Ctop_castSucc
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_A1Tail_eq_sourceReadbackSuffixState_Ctop_of_ne_zero
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_A1TailAfterFirst_eq_sourceReadbackSuffixState_Ctop_succ_zero
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_solvedA1_eq_topLeftCorner
```

## Reproduction

```text
reproduction-a2-retained-passive-source-recursive-reconstruction-spine.md
```

## Claim

For an arbitrary retained-passive-shaped edge family satisfying
`sourceRecursiveDetChart`, the source readback coordinates lie in the
retained-passive determinant chart.  Moreover, the readback's full right field
is the negative suffix-state `B` field, and its solved full `A1` family is the
selected top-left block of each visited transformed source edge.

The generic Schur reassembly lemma says that a block matrix with invertible
selected top-left corner is recovered from its one-step readbacks
`topLeftCorner`, `-(A1^-1 * upperRightBlock)`, `lowerLeftBlock`, and
`schurResidualBlock`.

## Method

The proof is finite suffix-state algebra.  Determinant units propagate
backward from the terminal state because
`S_{p.castSucc}.Ctop = S_{p.succ}.Ctop * topLeftCorner T_p`.  The `F2full`
identity unfolds the source readback and terminal suffix state.  The solved
`A1` identity uses a backward-induction invariant for every nonzero passive
tail:

```text
residualFactorProduct A1seed last i = S_i.Ctop.
```

At `i = succ 0`, this identifies the passive tail.  Multiplying the recurrence
`S_0.Ctop = S_1.Ctop * topLeftCorner T_0` on the left by `S_1.Ctop^-1`
recovers the missing active `A1_0`.

## Role

This is the first right-inverse reconstruction spine after the source-readback
continuity rung.  It prepares the future theorem

```text
edgeMatrix (sourceReadback E) = E
```

but intentionally does not state it yet.

## Nonclaims

No solved-`A3` endpoint reconstruction is proved here.  No full
`edgeMatrix (sourceReadback E) = E`, image openness, local homeomorphism,
source-rank coverage, source/image equality, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT extraction is
proved.

## Verification

Focused checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

Full-library and hygiene checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

Review:
`review-a2-retained-passive-source-recursive-reconstruction-spine.md`.
