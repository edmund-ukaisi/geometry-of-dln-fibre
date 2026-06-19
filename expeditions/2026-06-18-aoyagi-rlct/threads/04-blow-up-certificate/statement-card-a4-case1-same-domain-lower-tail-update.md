# Statement card - A4 Case 1 same-domain lower-tail update

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `10e5f74`.

Names:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.updateSelected`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.lowerTailVector_labelExponentCertificate`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.case1_selectedLowerTail_sameDomain`

## Statement

Lean proves a conditional certificate update, not a chart transition theorem.
At a fixed state `(S,J)`, one selected introduced label can be replaced by its
Case 1 lower-tail certificate while every other introduced label is assumed
unchanged.

The Case 1 package-level theorem assumes:

```text
old certificates over the introduced-label domain at (S,J),
Case1FirstJumpHypotheses for the selected label,
leastValue(s,k) = level(s,k),
FlatTailFromPred for the selected vector at level(s,k),
2 <= S <= L,
post selected vector = lowerTailVector oldVector S J,
post selected numerator = oldNumerator + J1 * (n_(S+1)-J),
post selected least value = J,
all non-selected introduced labels are unchanged.
```

The increment uses actual active width `n_(S+1)-J`, not a prefix minimum.

## Source role

This is the certificate bookkeeping behind Aoyagi Case 1(1), where the
selected old exceptional variable chart lowers the selected label from level
`J+J1` to level `J` and adds

```text
J1 * (n_(S+1)-J)
```

to its numerator. The theorem reuses the finite first-jump package and the
one-label lower-tail arithmetic. It stays at the same state `(S,J)`; it does
not add `(S,J+1)`, advance `J`, or advance `S`.

## Proved

- Same-domain certificate replacement for one introduced label.
- The selected Case 1 source level can feed the one-label lower-tail
  transformer when `leastValue = level` and `FlatTailFromPred` are supplied.
- Under assumed post-data, the all-introduced-label certificate package is
  reassembled at the same state `(S,J)`.
- Non-selected labels are carried by explicit unchanged-data hypotheses.

## Not proved

- No construction of the selected label or proof that a finite minimum exists.
- No proof of `leastValue = level` for the selected label.
- No proof of the selected label's flat-tail hypothesis.
- No proof that the chart produces the post assignments.
- No blow-up chart, coordinate pullback, row-strip division, Jacobian
  calculation, ideal equality, or chart coverage.
- No `b'_i` recurrence bookkeeping or proof that
  `b'_(J+1),...,b'_(J+J1)` are multiplied by the selected variable.
- No use of minimality to prove comparability or termination.
- No domain extension, no `(S,J+1)` label, and no `J` or `S` advance.
- No boundary case `S=1`; the theorem assumes `2 <= S <= L`.
- No normal-crossing certificate or RLCT extraction.

## Status

- Sorry-free and xhigh source-scope reviewed at `10e5f74`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
