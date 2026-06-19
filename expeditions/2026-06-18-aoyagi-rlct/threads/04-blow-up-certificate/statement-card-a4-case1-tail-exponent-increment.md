# Statement card - A4 Case 1 tail exponent increment

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `9c1b791`.

Names:

- `DLNFibre.DLN.Aoyagi.lowerTailVector`
- `DLNFibre.DLN.Aoyagi.lowerTailVector_eq_of_lt`
- `DLNFibre.DLN.Aoyagi.lowerTailVector_eq_of_le`
- `DLNFibre.DLN.Aoyagi.lowerTailVector_self`
- `DLNFibre.DLN.Aoyagi.le_lowerTailVector_of_le`
- `DLNFibre.DLN.Aoyagi.lowerTailVector_isLeast_valueSet_Icc`
- `DLNFibre.DLN.Aoyagi.FlatTailFromPred`
- `DLNFibre.DLN.Aoyagi.terminalExponent_lowerTailVector_of_flatFromPred`
- `DLNFibre.DLN.Aoyagi.FlatTailFromPred.terminalExponent_lowerTailVector`
- `DLNFibre.DLN.Aoyagi.terminalExponent_lowerTailVector_of_flatFromPred_add`
- `DLNFibre.DLN.Aoyagi.FlatTailFromPred.terminalExponent_lowerTailVector_add`
- `DLNFibre.DLN.Aoyagi.LabelExponentCertificate.lowerTailVector_of_flatFromPred_add`

## Statement

For a vector `T` whose tail is flat at value `h` from `S-1` through `L`,
lowering the entries from `S` onward to `J` changes the terminal exponent by

```text
(h - J) * (n_(S+1) - J).
```

In the Case 1 source form, when `h = J + J1`, the increment is

```text
J1 * (n_(S+1) - J).
```

Lean also packages the finite component facts for the lowered vector. If the
old vector is bounded below by `J`, then the lowered vector has least value
`J` on `1..L`. The one-label certificate transformer combines this least-value
fact with the terminal-exponent increment when the old one-label certificate
has least value `J+J1` and `J <= J+J1`.

## Source role

This is the arithmetic behind Aoyagi Case 1's exponent update when the chosen
label at level `J+J1` has its tail reset to `J`. The theorem isolates the
needed flat-tail hypothesis; that hypothesis must come from a later invariant.

## Proved

- The base term is unchanged under `2 <= S`.
- All summands except `j=S` are unchanged or vanish under the flat-tail
  hypotheses.
- The surviving summand gives the source increment.
- The lowered vector is unchanged before `S` and equal to `J` from `S` onward.
- Under an old lower bound by `J`, `J` is the finite least value on `1..L`.
- A single already-introduced label certificate can be re-certified after tail
  lowering, assuming old least value `J+J1`, flat tail, and `J <= J+J1`.

## Not proved

- No proof that a Case 1 selected label satisfies the flat-tail hypothesis.
- No proof that the old least value is `J+J1` for the selected label.
- No proof of the nonnegative-jump comparison `J <= J+J1`.
- No `IntroducedLabelExponentCertificates` all-label/domain transition.
- No chart construction, old-label update, Jacobian recurrence, comparability,
  transition theorem, termination proof, normal-crossing certificate, or RLCT
  extraction.
- The theorem intentionally excludes `S=1` and `S>L`, where the formula is not
  generally valid.

## Status

- Sorry-free and xhigh source-scope reviewed at `9c1b791`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
