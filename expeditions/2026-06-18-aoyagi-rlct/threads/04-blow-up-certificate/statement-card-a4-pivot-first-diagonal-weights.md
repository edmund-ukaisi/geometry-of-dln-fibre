# Statement card - A4 pivot-first diagonal weights

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`90ca2136357ae5927c462aedb69c47e17a52b21a`.

Name:

- `DLNFibre.DLN.Aoyagi.weightedPivotDiagonal_eq_pivotFirst_diagonal`

## Statement

Lean proves that the split diagonal row-weight matrix used by the pivot-first
`P` operation is exactly the original diagonal row-weight matrix reindexed into
pivot-first row coordinates.

## Source role

Aoyagi's displayed `P` matrix acts on diagonal monomial weights. The pivot-first
formalisation separates the pivot row from the other rows. This checkpoint
proves that this split diagonal is merely a reindexing of the original supplied
row-weight diagonal.

## Proved

```text
weightedPivotDiagonal (weight rowPivot)
  (fun i : pivotComplement rowPivot => weight i)
 =
(diagonal weight).submatrix
  (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv rowPivot).
```

## Assumed

- A supplied row-weight function `weight`.
- The selected pivot row `rowPivot`.

## Not proved

- No proof of Aoyagi recurrence flatness or row-weight assignment from source
  variables.
- No quotient-witness theorem beyond existing separate wrappers.
- No selected-entry chart construction, chart coverage, exponent update,
  transition invariant, normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-pivot-first-diagonal-weights-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
