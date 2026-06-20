# Statement card - A4 Case 2 printed mismatch boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.terminalExponent_printedCase2Vector_sub_prefixFormula`
- `DLNFibre.DLN.Aoyagi.terminalExponent_printedCase2Vector_eq_prefixFormula_iff`
- `DLNFibre.DLN.Aoyagi.terminalExponent_case2Printed_ne_corrected_of_prefixDrop_of_cont`

## Statement

Lean now isolates the exact boundary where Aoyagi's printed Case 2 vector can
match the prefix-minimum terminal exponent formula.

The exact difference is:

```text
terminalExponent(printed vector) - (prefixMin n S - J)(n_(S+1)-J)
  = (n_S - prefixMin n S)(n_(S+1)-J).
```

Over natural widths, equality with the prefix formula holds iff:

```text
n_S = prefixMinNat n S
or
n_(S+1) = J.
```

Under the Case 2 continuation bound `J+1 <= prefixMinNat n (S+1)`, the second
case cannot occur. Hence if `prefixMinNat n S < n S`, the printed vector and
the corrected prefix-minimum vector have different terminal exponents.

## Source Role

This is a source-gap boundary theorem. It makes precise the existing repair
note: the PDF's printed vector uses actual earlier widths, while the printed
Case 2 numerator increment uses the prefix minimum. The theorem does not say
which repair is source-authoritative; it states exactly when the printed data
are mutually compatible.

## Proved

- Exact difference between the printed-vector terminal exponent and the
  prefix-minimum Case 2 increment.
- Equality characterization including the degenerate zero-column-factor case.
- Genuine mismatch under prefix-width drop plus the Case 2 continuation bound.

## Not Proved

- No Case 2 transition theorem.
- No reachable-state proof that `prefixMinNat n S = n S`.
- No erratum claim.
- No chart construction, pivot coverage, regularity, Jacobian, normal
  crossings, RLCT extraction, or termination.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-printed-mismatch-boundary-a4.md`.
- Review artifact:
  `review-case2-printed-mismatch-boundary-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
