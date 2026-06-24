# Review - A2 regular/residual ideal split

Date: 2026-06-24.

Reviewers: controller check, xhigh scouts `Kant the 3rd` and `Planck the 3rd`.

## Verdict

Passed.

The split theorem is pure ideal algebra: `regularBlockEntryIdeal` names the
join of entry ideals for `X`, `F2`, and `F3`, and `fourMatrixEntryIdeal` is
defined as that regular ideal joined with `matrixEntryIdeal D`.  The primitive
split theorem is therefore `rfl`.

The canonical corollaries preserve the source sign convention:

```text
F2 = -S.B,
F3 = lowerLeftBlock S.L.
```

They keep `S.D` as a residual block and do not add it to the regular-coordinate
index.

## Build Check

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/EntryIdeal.lean
lake build DLNFibre.DLN.Aoyagi.EntryIdeal
lake env lean DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean
```

These focused checks passed.

## Remaining Gate

Run the broader import, sorry, and whitespace gates before banking the current
dirty expedition stack.
