# Review - Lemma 5 equation (4) piecewise certificate

Reviewer: xhigh `Singer`.

Status: passed after minor wording polish.

## Findings

No blocking findings.

The equation `(4)` branch translation is source-faithful.  The zero-based
block index `b` corresponds to source `j=b+1`, so the source branch
`2<=j<=p+1` becomes `1<=b<=p` with value `Htilde'_b-b`.  The own coordinate
`S_(p+1)-1` lands in block `b=p`.

The record does not overclaim existence, terminality, chart coverage, or total
source-layer coverage.  It is a conditional branch certificate, and the
module/card nonclaims are explicit.

The theorem hypotheses are sufficient for the stated conclusion.  The theorem
correctly proves label legality against the selected-width array `m`, not
against an actual `layerWidth` value.

## Minor Polish Applied

- Clarified that `AoyagiSelectedCutpoints.cut` stores source selected indices
  `S_(i+1)` indexed zero-based in Lean, not zero-based source values.
- Added an explicit deferred caveat that future theorems comparing selected
  widths with actual layer widths need a compatibility hypothesis such as
  `m i = layerWidth(point C i)`.

## Nonclaims

- No construction or existence proof for the displayed vector.
- No total source-layer coverage.
- No terminal `tilde t=0`.
- No vector admissibility or source vector-to-chain correspondence.
- No Case 1(2) chart sequence.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
