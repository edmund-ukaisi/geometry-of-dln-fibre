# Statement Card - Definition 3 nonconstant `(1,2,2)` example

## Lean Target

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`
- Reproduction:
  `threads/06-dln-translation/reproduction-definition3-nonconstant-one-two-two-example-a6.md`

## Claim

For `L=2`, `r=0`, and source-range reduced widths `(1,2,2)`, consecutive
all-source selected cutpoints produce Definition 3 source data, selected
reduced widths, and a Definition 3 ceiling datum.  The selected width family
is nonconstant: `m 0 = 1`, `m 1 = 2`, and `m 0 != m 1`.

## Scope

This is a diagnostic example showing that the all-source selected constructor
is broader than the equal-width lane.  It does not classify Definition 3,
prove arbitrary cutpoint existence, compute closed-form ceiling data, produce
Eq5 payloads, charts, pole order, or RLCT.

## Verification

Focused Lean check passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Review:
`threads/06-dln-translation/review-definition3-nonconstant-one-two-two-example-a6.md`.
