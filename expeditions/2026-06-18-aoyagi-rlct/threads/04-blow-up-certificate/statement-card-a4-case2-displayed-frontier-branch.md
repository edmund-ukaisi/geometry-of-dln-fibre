# Statement card - A4 Case 2 displayed frontier branch

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedStepBranch`
- `DLNFibre.DLN.Aoyagi.case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont`
- `DLNFibre.DLN.Aoyagi.case2DisplayedStepBranch_of_cont`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.frontierBranch`

## Statement

Lean records the finite frontier alternatives after Aoyagi's displayed Case 2
pivot.  Under the current displayed-pivot validity
`J+1 <= prefixMinNat n (S+1)`, either the next same-stage center has a possible
entry `J+2`, or one stopped side has frontier value `J+1`:

```text
J+2 <= prefixMinNat n (S+1)
or n(S+1)=J+1
or prefixMinNat n S=J+1.
```

The displayed supplied boundary exports this as a `Case2DisplayedStepBranch`.

## Proved

- The next-continuation alternative is exactly the finite nonempty lower-right
  post-pivot domain condition already proved for Case 2.
- If the next-continuation alternative fails but the displayed pivot is valid,
  the prefix frontier is `J+1`, hence either actual next-width exhaustion or
  current-prefix row exhaustion holds.
- The supplied displayed boundary exposes the resulting finite branch witness.

## Assumed

- Only the finite hypotheses in the theorem statements: `1 <= S` and displayed
  pivot validity.
- For the namespace projection, the existing supplied displayed boundary.

## Cited

- None in Lean.  This is finite natural-number arithmetic.

## Deferred

- Branch-specific terminal/source product packages are still the existing
  separate theorems.
- Chart construction, post-data production, successor chart-family data,
  transition invariance, Jacobian arithmetic, normal crossings, pole order, and
  RLCT extraction remain separate.

## Review

- xhigh pen-and-paper scout `Aristotle` reproduced the finite frontier
  arithmetic.
- xhigh Lean API scout `Copernicus` confirmed there was no pre-existing branch
  witness datatype and identified this as the minimal reusable Lean layer.
- xhigh hardener `Hubble` warned not to name the result as an exhaustive split
  or to attach original-row/relabel conclusions to the row-exhausted branch.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
