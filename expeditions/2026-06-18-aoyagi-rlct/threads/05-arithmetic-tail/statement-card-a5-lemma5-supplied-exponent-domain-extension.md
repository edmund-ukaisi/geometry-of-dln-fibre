# Statement Card - A5 Lemma 5 Supplied Exponent-Domain Extension

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_extendExponentDomain_succ_current_of_lastPoint_widthBound`

## Claim

For one supplied Eq4, Eq3, or Eq5 branch whose label is `J+1`, the source-label
wrappers supply the new label's `introducedLabel` field at state `(S,J+1)`.
If the new label's terminal exponent equality and least-value proof are also
supplied, then the all-introduced-label exponent-certificate family extends
from `(S,J)` to `(S,J+1)`.

## Inputs

- Existing source-label hypotheses for the selected branch.
- Prior `IntroducedLabelExponentCertificates L n S J t numerator leastValue`.
- Supplied new-label terminal-exponent equality:

```text
terminalExponent L (widthZ n) (t' S (J+1)) = numerator' S (J+1)
```

- Supplied new-label least-value proof:

```text
IsLeast {v | exists i in Icc 1 L, t' S (J+1) i = v}
  (leastValue' S (J+1))
```

- Old introduced labels preserve vector, numerator, and least-value data.
- Eq3 keeps the explicit one-unit slack.
- Eq5 keeps the explicit own-block actual-width lower bound.

## Proves

Only the one-step extension of
`IntroducedLabelExponentCertificates` over the source-shaped Eq3, Eq4, and Eq5
branch labels.

## Does Not Prove

- The terminal-exponent formula for any branch.
- The least-value theorem for any branch.
- Construction of Eq3/Eq4/Eq5 displayed vectors or all branch families.
- Any chart production, terminality, admissibility, chart coverage, Lemma 5
  order count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(3)`, `(4)`, and `(5)`, PDF pp. 26-27, plus the
generic exponent-domain extension theorem
`IntroducedLabelExponentCertificates.extendDomain_succ_current`.
