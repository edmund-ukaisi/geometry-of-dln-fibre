# Statement card - A4 finite exponent-domain bookkeeping

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `2586b46`.

Names:

- `DLNFibre.DLN.Aoyagi.LabelExponentCertificate`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.labelExponentCertificate`
- `DLNFibre.DLN.Aoyagi.introducedLabel_succ_cases`
- `DLNFibre.DLN.Aoyagi.introducedLabel_succ_iff`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.extendDomain_succ_current`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_bounds`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_prefixBound`

## Statement

Lean now has a Prop-valued container for finite exponent data over the
introduced-label domain. A one-label certificate records:

```text
introduced label,
terminal exponent of its vector,
least value of that vector on 1..L.
```

`IntroducedLabelExponentCertificates` packages such certificates for all labels
introduced at a state `(S,J)`. The extension lemmas are domain-extension
bookkeeping: if old label assignments are unchanged and the new current-layer
label `(S,J+1)` has a certificate, then the package extends to state
`(S,J+1)`.

## Source role

This is a finite container needed for a later corrected vector invariant. It
uses actual-width introduced labels as the domain and keeps the corrected
Case 2 new-label certificate as a one-label input.

## Proved

- A `J`-advance changes the introduced domain only at `(S,J+1)`.
- The corrected Case 2 new-label certificate can be viewed as a generic
  `LabelExponentCertificate`.
- A certificate package over `(S,J)` extends to `(S,J+1)` when old data is
  definitionally supplied as unchanged and the new label is certified.
- The corrected Case 2 one-label certificate supplies that new-label input
  under either separate actual/state bounds or the stronger continuation bound.

## Not proved

- No blow-up transition theorem.
- No proof that the old assignments are unchanged by a chart.
- No corrected vector assignment for every actual-width introduced label.
- No pairwise comparability, Jacobian recurrence, chart coverage, termination,
  normal-crossing certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh source-scope reviewed at `2586b46`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
