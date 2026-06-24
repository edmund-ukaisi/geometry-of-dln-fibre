# Statement Card - Definition 3 all-source selected ceiling data

## Lean Target

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`
- Reproduction:
  `threads/06-dln-translation/reproduction-definition3-all-source-ceil-data-a6.md`

## Claim

If `0<L`, source-range rank-width holds, and every source-range reduced width
satisfies the strict all-source selected inequality, then consecutive
all-source cutpoints produce:

- `AoyagiDefinition3SourceData L L H r C`;
- the selected reduced-width family `m`;
- a Definition 3 ceiling datum `data`;
- Nat-width rewrites, nonnegativity, strict selected inequalities, selected
  upper bounds, and Nat selected-width nonnegativity.

## Scope

This packages the all-source selected constructor with the existing
rank-width ceiling-data package.  It does not compute `ceilWidth` or `aParam`,
prove arbitrary selected-cutpoint existence, classify Definition 3, construct
Eq5 payloads, produce charts, identify pole order, or extract RLCT.

## Verification

Focused Lean check passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Review:
`threads/06-dln-translation/review-definition3-all-source-ceil-data-a6.md`.
