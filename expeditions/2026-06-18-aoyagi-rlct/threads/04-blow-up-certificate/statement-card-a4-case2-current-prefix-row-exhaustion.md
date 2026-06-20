# Statement card - A4 Case 2 current-prefix row exhaustion

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplement_isEmpty_of_prefixMin_current_eq`

## Statement

Lean now proves that current-prefix row exhaustion

```text
prefixMinNat n S = J+1
```

empties the displayed Case 2 pivot's row complement.

## Proved

- Post-pivot displayed residual rows are empty under current-prefix
  exhaustion.
- Therefore the displayed pivot row complement is empty.

## Assumed

- Displayed pivot validity `J+1 <= prefixMinNat n (S+1)`.
- Current-prefix row exhaustion `prefixMinNat n S=J+1`.

## Not Proved

- No actual-width exhaustion claim.
- No column-complement emptiness claim.
- No projection from the actual-width terminal source model.
- No construction of `C'^(S+1)`.
- No source-produced terminal following matrix.
- No chart production, chart coverage or regularity, Jacobian arithmetic,
  normal crossings, RLCT extraction, termination, transition invariant,
  automatic Case 2 gap/tail transport, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-current-prefix-row-exhaustion-a4.md`.
- Review artifact:
  `review-case2-current-prefix-row-exhaustion-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
