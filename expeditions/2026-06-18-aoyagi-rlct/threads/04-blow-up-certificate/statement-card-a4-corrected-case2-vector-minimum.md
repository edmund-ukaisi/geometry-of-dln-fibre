# Statement card - A4 corrected Case 2 vector minimum

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.prefixMinNat_succ_le`
- `DLNFibre.DLN.Aoyagi.prefixMinNat_antitone`
- `DLNFibre.DLN.Aoyagi.correctedCase2PivotVector_apply`
- `DLNFibre.DLN.Aoyagi.correctedCase2PivotVector_eq_prefix_of_lt`
- `DLNFibre.DLN.Aoyagi.correctedCase2PivotVector_eq_J_of_le`
- `DLNFibre.DLN.Aoyagi.correctedCase2PivotVector_self`
- `DLNFibre.DLN.Aoyagi.le_correctedCase2PivotVector_of_le_prefixMinNat`
- `DLNFibre.DLN.Aoyagi.correctedCase2PivotVector_min_certificate`
- `DLNFibre.DLN.Aoyagi.correctedCase2PivotVector_isLeast_valueSet_Icc`

## Statement

For the corrected Case 2 vector

```text
t^i = mu_(i+1)  for i < S,
t^i = J         for i >= S,
```

Lean proves the component formulas and the finite lower-bound certificate:
if `J <= mu_S`, then every component of the corrected vector is at least `J`,
and the component at `S` is exactly `J`. If also `1 <= S <= L`, Lean proves
that `J` is the least value attained by the vector on the source range
`1..L`.

## Source role

This is the finite bookkeeping behind the repaired Case 2 line
`\tilde t_(S,J+1)=J`. It uses the corrected prefix-minimum vector, not the
actual-width vector printed in the PDF.

## Proved

- Prefix minima are antitone as the prefix grows.
- The corrected vector is `mu_(i+1)` before `S`.
- The corrected vector is `J` from `S` onward.
- Under the state bound `J <= mu_S`, `J` is a lower bound for all total
  components and is attained at component `S`.
- On the finite source component range `1..L`, with `1 <= S <= L`, the value
  set has least element `J`.

## Not proved

- No pairwise comparability of all vector labels.
- No assignment of vector/exponent data to every introduced label.
- No Case 1/2 transition theorem.
- No pivot-chart coverage, termination proof, normal-crossing certificate, or
  RLCT extraction.

## Status

- Sorry-free.
- Commit SHA pin pending until the Lean-theorem commit exists.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
