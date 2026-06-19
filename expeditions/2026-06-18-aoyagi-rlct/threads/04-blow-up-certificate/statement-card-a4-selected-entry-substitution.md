# Statement card - A4 selected-entry substitution scaffold

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `ba22b5b`.

Names:

- `DLNFibre.DLN.Aoyagi.selectedEntryChartMap`
- `DLNFibre.DLN.Aoyagi.selectedEntryChartMap_pivot`
- `DLNFibre.DLN.Aoyagi.selectedEntryChartMap_of_ne`
- `DLNFibre.DLN.Aoyagi.selectedEntryChartMap_pivot_dvd`
- `DLNFibre.DLN.Aoyagi.selectedEntryChartMap_pivot_mem_valueSet`
- `DLNFibre.DLN.Aoyagi.case2_displayedPivot_selectedEntryChartMap_value_mem`

## Statement

Lean now records the finite algebraic substitution pattern for one selected
generator of a center:

```text
selected generator -> u,
other generator i  -> u * residual_i.
```

It proves that the selected generator maps to `u`, every transformed generator
is divisible by `u`, and the value `u` occurs in the finite value set whenever
the selected generator belongs to the center. For the corrected Case 2
residual-block entry set, the displayed source pivot `(J+1,J+1)` supplies such
a value under the continuation bound.

## Source role

This is the algebraic substitution pattern in Aoyagi's displayed pivot charts:
the selected center generator is used as the exceptional variable and the other
center generators are divided by it.

## Proved

- Generic selected-entry substitution values at the pivot and away from it.
- Divisibility of every transformed center generator by the selected pivot
  variable.
- Occurrence of the pivot value in the finite value set.
- Case 2 displayed-pivot specialization for the residual-block entry set.

## Not proved

- No blow-up chart construction.
- No chart cover theorem.
- No proof for non-displayed selected entries' `Q/P` transition formulas.
- No polynomial regularity, Jacobian/unit facts, transition invariant,
  termination proof, normal-crossing certificate, or RLCT extraction.
- No Case 1 center type combining the selected old exceptional variable with
  residual-block entries.

## Status

- Sorry-free and xhigh source-scope reviewed at `ba22b5b`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
