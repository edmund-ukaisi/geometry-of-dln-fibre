# Statement Card - Definition 3 all-source selected source data

## Lean Target

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_of_all_selected_strict`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`
- Reproduction:
  `threads/06-dln-translation/reproduction-definition3-all-source-selected-source-data-a6.md`

## Claim

If `0 < L` and every source-range reduced width satisfies the strict
all-source selected inequality

```text
L * M^(s) < sum_{j : Fin (L+1)} M^(j.val+1),
```

then consecutive cutpoints `C.cut j = j.val+1` give
`AoyagiDefinition3SourceData L L H r C`.

## Scope

Every source layer is selected, so the nonselected fields are vacuous at the
selected-width-value level.  The theorem does not assume rank-width,
positivity, or constant widths.  It does not construct arbitrary selected
cutpoints, classify Definition 3, produce a ceiling datum, construct Eq5
payloads, produce charts, or prove pole order/RLCT.

## Verification

Focused Lean check passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Review:
`threads/06-dln-translation/review-definition3-all-source-selected-source-data-a6.md`.
