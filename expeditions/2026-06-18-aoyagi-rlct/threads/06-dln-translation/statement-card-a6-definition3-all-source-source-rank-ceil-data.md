# Statement Card - Definition 3 all-source source-rank ceiling data

## Lean Target

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_sourceRankStratum`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/Definition3RankWidthBridge.lean`
- Reproduction:
  `threads/06-dln-translation/reproduction-definition3-all-source-source-rank-ceil-data-a6.md`

## Claim

Under A2 source-rank-stratum membership and the dimension convention
`H(k.val+1)=finrank(W k)`, the strict all-source selected inequality produces
consecutive all-source cutpoints, Definition 3 source data, selected reduced
widths, and a Definition 3 ceiling datum with the standard package fields.

## Scope

This is a single source-rank wrapper around the all-source strict/rank-width
ceiling-data theorem.  It does not prove the strict inequality, source-rank
membership, exact-rank openness, chart coverage, closed-form ceiling data, Eq5
payloads, pole order, or RLCT.

## Verification

Focused Lean check passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3RankWidthBridge.lean
```

Review:
`threads/06-dln-translation/review-definition3-all-source-source-rank-ceil-data-a6.md`.
