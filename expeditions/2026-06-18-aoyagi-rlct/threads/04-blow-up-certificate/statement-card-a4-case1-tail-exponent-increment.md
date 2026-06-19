# Statement card - A4 Case 1 tail exponent increment

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `70badc4`.

Names:

- `DLNFibre.DLN.Aoyagi.lowerTailVector`
- `DLNFibre.DLN.Aoyagi.terminalExponent_lowerTailVector_of_flatFromPred`
- `DLNFibre.DLN.Aoyagi.terminalExponent_lowerTailVector_of_flatFromPred_add`

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

## Source role

This is the arithmetic behind Aoyagi Case 1's exponent update when the chosen
label at level `J+J1` has its tail reset to `J`. The theorem isolates the
needed flat-tail hypothesis; that hypothesis must come from a later invariant.

## Proved

- The base term is unchanged under `2 <= S`.
- All summands except `j=S` are unchanged or vanish under the flat-tail
  hypotheses.
- The surviving summand gives the source increment.

## Not proved

- No proof that a Case 1 selected label satisfies the flat-tail hypothesis.
- No chart construction, old-label update, Jacobian recurrence, comparability,
  transition theorem, termination proof, normal-crossing certificate, or RLCT
  extraction.
- The theorem intentionally excludes `S=1` and `S>L`, where the formula is not
  generally valid.

## Status

- Sorry-free and xhigh pen-and-paper checked at `70badc4`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
