# Statement card - A4 corrected Case 2 new-label certificate

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `d3f2be6`.

Names:

- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate`
- `DLNFibre.DLN.Aoyagi.correctedCase2NewLabelCertificate_of_actualBound_of_stateBound`
- `DLNFibre.DLN.Aoyagi.correctedCase2NewLabelCertificate_of_prefixBound`

## Statement

For the corrected Case 2 new label `(S,J+1)`, Lean packages three finite
facts:

```text
(S,J+1) is introduced after the pivot advance,
E(correctedCase2PivotVector n S J) = (mu_S-J)(n_(S+1)-J),
J is the least value of correctedCase2PivotVector n S J on 1..L.
```

The main theorem assumes the exact separate bounds needed for these facts:
`J+1 <= n_(S+1)` for actual source-label validity, and `J <= mu_S` for the
minimum certificate. The continuation-bound corollary derives both from
Aoyagi's stronger condition `J+1 <= mu_(S+1)`.

## Source role

This is corrected finite bookkeeping for the new Case 2 label only. It uses
the prefix-minimum repaired vector, not the actual-width vector printed in the
PDF.

## Proved

- The corrected Case 2 new label is introduced after advancing from `J` to
  `J+1`, under the actual-width label bound.
- The corrected new label has the repaired terminal-exponent contribution
  `(mu_S-J)(n_(S+1)-J)`.
- Under the state bound `J <= mu_S`, the corrected vector has least value `J`
  on the source component range.
- The source continuation bound `J+1 <= mu_(S+1)` is a sufficient combined
  hypothesis.

## Not proved

- No data assignment for every introduced label.
- No claim about the PDF's printed Case 2 vector.
- No pairwise comparability of vectors.
- No Case 1/2 transition theorem.
- No pivot-chart coverage, termination proof, normal-crossing certificate, or
  RLCT extraction.

## Status

- Sorry-free and xhigh reviewed at `d3f2be6`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
