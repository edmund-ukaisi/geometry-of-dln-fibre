# Statement card - A4 Case 2 actual-width column exhaustion

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplement_isEmpty_of_width_next_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.displayedPivotColComplement_isEmpty`

## Statement

Lean now proves that actual next-width exhaustion

```text
n(S+1) = J+1
```

empties the displayed Case 2 pivot's column complement.  The source-model
projection exposes the same fact from a
`Case2DisplayedSuppliedActualWidthTerminalSourceModel`.

## Proved

- Post-pivot displayed residual columns are empty under actual-width
  exhaustion.
- Therefore the displayed pivot column complement is empty.
- The actual-width terminal source model exports this column-complement
  emptiness.

## Assumed

- Displayed pivot validity `J+1 <= prefixMinNat n (S+1)`.
- Actual next-width exhaustion `n(S+1)=J+1`.

## Not Proved

- No construction of `C'^(S+1)`.
- No source-produced terminal following matrix.
- No row-complement emptiness claim.
- No chart production, chart coverage or regularity, Jacobian arithmetic,
  normal crossings, RLCT extraction, termination, transition invariant,
  automatic Case 2 gap/tail transport, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-actual-width-column-exhaustion-a4.md`.
- Review artifact:
  `review-case2-actual-width-column-exhaustion-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
