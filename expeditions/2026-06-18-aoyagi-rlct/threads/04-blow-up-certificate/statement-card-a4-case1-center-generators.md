# Statement card - A4 Case 1 center generators

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `75049ad`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1CenterGenerator`
- `DLNFibre.DLN.Aoyagi.case1StripRows`
- `DLNFibre.DLN.Aoyagi.case1StripCols`
- `DLNFibre.DLN.Aoyagi.case1StripEntries`
- `DLNFibre.DLN.Aoyagi.case1CenterGenerators`
- `DLNFibre.DLN.Aoyagi.mem_case1StripRows`
- `DLNFibre.DLN.Aoyagi.mem_case1StripCols`
- `DLNFibre.DLN.Aoyagi.mem_case1StripEntries_iff`
- `DLNFibre.DLN.Aoyagi.case1_selectedOld_mem_center`
- `DLNFibre.DLN.Aoyagi.case1_stripEntry_mem_center`
- `DLNFibre.DLN.Aoyagi.case1_displayedPivot_mem_center_of_bounds`
- `DLNFibre.DLN.Aoyagi.case1_selectedOld_selectedEntryChartMap_value_mem`
- `DLNFibre.DLN.Aoyagi.case1_displayedPivot_selectedEntryChartMap_value_mem`

## Statement

After the old exceptional variable has been chosen externally, Lean represents
the finite Case 1 center by a sum type:

```text
Unit        = the chosen old exceptional generator,
Nat x Nat   = a row-strip entry d_ij.
```

The row strip is indexed by

```text
J+1 <= i <= J+J1,
J+1 <= j <= n_(S+1).
```

Lean proves membership criteria for rows, columns, and strip entries, proves
that the chosen old generator belongs to the center, and proves that Aoyagi's
displayed pivot entry `(J+1,J+1)` belongs under the entry bounds
`1 <= J1` and `J+1 <= n_(S+1)`.

## Source role

This records the generator set for the Case 1 blow-up center:

```text
d_ij = 0 for the row strip,
u_(s,k) = 0 for the chosen old exceptional variable.
```

The column range uses the actual active width `n_(S+1)`, not the prefix
minimum.

## Proved

- Finite row-strip entry indexing.
- Finite center generator symbols combining the chosen old exceptional
  generator and row-strip entries.
- Membership of the chosen old generator.
- Membership of row-strip generators.
- Displayed pivot-entry membership under the finite entry bounds.
- Selected-entry value-set specializations for the selected-old-variable chart
  and the displayed pivot-entry chart.

## Not proved

- The `Unit` branch does not encode the old label `(s,k)`, actual-width
  validity, level `J+J1`, minimality, or comparability.
- No proof that the whole row strip is source-valid in the active residual
  rows; a later statement may need `J+J1 <= mu_S`.
- No chart coverage, non-displayed pivot transition, `Q/P` transition,
  regularity/Jacobian fact, exponent update, transition invariant,
  termination proof, normal-crossing certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh source-scope reviewed at `75049ad`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
