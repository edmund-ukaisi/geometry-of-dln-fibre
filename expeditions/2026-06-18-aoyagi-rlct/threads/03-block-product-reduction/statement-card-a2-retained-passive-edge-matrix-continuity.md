# Statement Card - A2 retained-passive edge-matrix continuity

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype_apply
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype
```

## Reproduction

```text
reproduction-a2-retained-passive-edge-matrix-continuity.md
```

## Claim

On the nonredundant determinant-chart subtype, every retained-passive
fixed-base edge matrix component is continuous:

```text
data -> data.1.edgeMatrix p.
```

Consequently the whole finite edge family

```text
data -> data.1.edgeMatrix
```

is continuous in the Pi topology.

## Method

Unfold `edgeMatrix` to the fixed-base formula

```text
fromBlocks 1 (F2 p.succ) 0 1 *
fromBlocks
  (solvedA1 p)
  (-(solvedA1 p * F2 p.castSucc))
  (solvedA3 p)
  (C p - solvedA3 p * F2 p.castSucc).
```

The proof composes already banked continuity of `solvedA1`, `solvedA3`,
`F2full`, and `C` with matrix multiplication, negation, subtraction, and
`fromBlocks` continuity.  The family statement uses componentwise Pi
continuity.

## Role

This is the first continuity theorem for the retained-passive source map on
the determinant chart.  It follows the determinant-domain and solved-endpoint
continuity rungs and prepares later source-image or transport statements
without proving them.

## Nonclaims

No image openness, source-rank coverage, source/image equality, local
homeomorphism, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT extraction is proved.

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
`Galileo the 3rd` and passed.  Review:
`review-a2-retained-passive-edge-matrix-continuity.md`.
