# Statement card - A4 terminal exponent split

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.terminalExponent`
- `DLNFibre.DLN.Aoyagi.printedCase2Vector`
- `DLNFibre.DLN.Aoyagi.prefixMin`
- `DLNFibre.DLN.Aoyagi.prefixCase2Vector`
- `DLNFibre.DLN.Aoyagi.prefixMin_step_factor_zero`
- `DLNFibre.DLN.Aoyagi.terminalExponent_printedCase2Vector`
- `DLNFibre.DLN.Aoyagi.terminalExponent_prefixCase2Vector`

## Statement

For an arbitrary integer-valued actual-width sequence `n`, stage `S`, and
pivot level `J`, Aoyagi's terminal exponent expression evaluates differently
on the printed Case 2 vector and on the corrected prefix-minimum vector.

The printed Case 2 vector is

```text
t^i = n_(i+1) for i < S,     t^q = J for q >= S.
```

Lean proves:

```text
terminalExponent L n (printedCase2Vector n S J)
  = (n S - J) * (n (S+1) - J).
```

The corrected prefix-minimum vector is

```text
t^i = prefixMin n (i+1) for i < S,     t^q = J for q >= S.
```

Lean proves:

```text
terminalExponent L n (prefixCase2Vector n S J)
  = (prefixMin n S - J) * (n (S+1) - J).
```

The hypotheses are `1 <= S` and `S <= L`; the functions are total on `Nat` to
keep this arithmetic layer independent of a later finite stage/index API.

## Source role

This is a source-gap isolating theorem, not a source theorem.  Page-image
inspection and xhigh source/pen-and-paper rechecks confirm that Aoyagi's PDF
prints the actual-width vector in Case 2 but prints the prefix-minimum
Jacobian update.  The Lean theorem records both sides without asserting the
full blow-up transition.

## Proved

- The printed vector evaluates to the actual-width expression
  `(M^(S)-J)(M^(S+1)-J)`.
- The prefix-minimum vector evaluates to the printed update
  `(M(S)-J)(M^(S+1)-J)`.
- The prefix-minimum pre-`S` summands vanish because
  `mu_(j+1)=min(mu_j,n_(j+1))`.

## Not proved

- No blow-up chart construction.
- No pivot-chart coverage.
- No regularity/divisibility proof for `P`.
- No termination argument.
- No normal-crossing certificate and no RLCT extraction.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`: `0 sorry, 0 #exit, 0 native_decide, 0 axiom`
