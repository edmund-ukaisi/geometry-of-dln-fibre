# Review - A2 suffix-step raw-order inverse density handoff

Date: 2026-06-26.

Verdict: accepted at the stated local product-step scope after two low fixes.

Reviewer: xhigh `Pascal the 2nd`.

## Checks

- The target tuple order is the raw-shaped target order
  `(Ctop,D,F3,A1,F2,A3,C)`.
- The arbitrary raw step tuple is read as
  `(S.Ctop,S.D,F3prev,A1,A2,A3,A4)`, where `A1,A2,A3,A4` are the transformed
  edge blocks.
- Determinant-chart membership uses exactly determinant-unit hypotheses for
  `S.Ctop` and the transformed edge top-left block.
- `S.D` is not assumed invertible.  It is passive in the determinant chart and
  appears only multiplicatively in the coordinate formulas.
- `transformedEdge` and `stepRawCoordinates` are used in the expected
  orientation.
- The continuity hypotheses are fieldwise and honest for the fields used:
  `E p`, `S.B`, `S.Ctop`, `S.D`, and `F3prev`.

## Review Fixes

- Corrected the reproduction and controller summaries to say that the formulas
  invert `A1` and `S.Ctop*A1`; `S.Ctop` is a unit hypothesis used to make the
  product a unit, not a separately displayed inverse in the forward target
  formula.
- Moved the new aggregate import to the end of `DLNFibre.lean`, following the
  local aggregator convention.

## Verification

Reviewer ran:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/ProductReductionStepSuffixDensity.lean
```

Controller focused and aggregate `scripts/lb` checks passed separately.

## Boundary

This checkpoint is local product-step chart/density infrastructure.  It does
not prove source coverage, product-chart construction for the original DLN
source, product-step pushforward, source/prior transport, signed-box density
identification, normal crossings, pole order, or RLCT.
