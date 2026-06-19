# Statement card - A4 level/tail invariant bridge

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `e3a06f8`.

Names:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelLevelTailInvariants`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelLevelTailInvariants.leastValue_eq_level`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelLevelTailInvariants.flatTail_abovePivot`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_levelTailInvariants`

## Statement

Lean packages a conditional bridge between source levels and the finite
certificate data. At a state `(S,J)`, the package assumes:

```text
leastValue(s,k) = level(s,k) for every introduced label,
FlatTailFromPred holds for every introduced label with J < level(s,k).
```

The Case 1 corollary uses these assumptions to apply the selected-label
lower-tail update-data theorem without separately supplying
`leastValue = level` and `FlatTailFromPred` for the selected label.

## Source role

This is an invariant fragment, not a proved invariant. It isolates the bridge
facts needed for the Case 1(1) selected old label: the source natural-valued
level agrees with the integer least value in the certificate, and labels above
the current pivot have the flat predecessor/tail shape needed by the
lower-tail exponent arithmetic.

Flat-tail is intentionally restricted to labels with `J < level`. It is not
claimed for all introduced labels, since current-stage labels can have
predecessor component data that is not equal to their current source level.

## Proved

- The bridge package supplies `leastValue = level` for the selected Case 1
  label because `Case1FirstJumpHypotheses` includes introducedness.
- The selected Case 1 label satisfies the above-pivot condition by
  `Case1FirstJumpHypotheses.lt_selectedLevel`.
- Therefore the selected lower-tail update-data theorem applies from the
  bridge package plus `2 <= S <= L`.

## Not proved

- No proof that Aoyagi's recursion establishes or preserves this bridge.
- No proof of `leastValue = level`; it is assumed.
- No proof that every above-pivot introduced label has the flat-tail shape; it
  is assumed.
- No claim that all introduced labels have flat predecessor tails.
- No initial-state boundary theorem for `S=1`; the selected update still
  assumes `2 <= S <= L`.
- No chart construction, chart coverage, row-strip division, Jacobian or
  `b'_i` bookkeeping, transition invariant, termination proof, normal-crossing
  certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh source-scope reviewed at `e3a06f8`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
