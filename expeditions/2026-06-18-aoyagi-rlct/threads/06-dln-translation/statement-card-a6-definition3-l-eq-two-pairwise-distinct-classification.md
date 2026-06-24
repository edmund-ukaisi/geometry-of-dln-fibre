# Statement Card - Definition 3 `L=2` pairwise-distinct classification

## Lean Targets

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.cut_eq_consecutive_of_L_eq_two`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`
- Reproduction:
  `threads/06-dln-translation/reproduction-definition3-l-eq-two-pairwise-distinct-classification-a6.md`

## Claim

For `L=2`, if the three source-range reduced widths are pairwise distinct and
rank-width nonnegative, then any Definition 3 source-data choice must have
`ell=2` and consecutive cutpoints `1,2,3`.  Consequently source-data existence
is equivalent to the all-source strict selected inequalities.

## Scope

This is finite Definition 3 structure only.  It does not classify repeated
widths, prove arbitrary selected-cutpoint existence, compute closed-form
ceiling data, produce Eq5 payloads, construct charts, identify pole order, or
extract RLCT.

## Verification

Focused Lean check passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
lean/scripts/sorries
git diff --check
```

Review passed:
`threads/06-dln-translation/review-definition3-l-eq-two-pairwise-distinct-classification-a6.md`.
