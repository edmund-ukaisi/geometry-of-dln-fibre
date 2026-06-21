# Statement Card - A4 Case 2 Row-Exhausted Source-Suffix Payload

## Lean Names

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_rowExhausted_sourceSuffixTransportedPrefixBoundary_withFiniteCenterIdeal`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedSourceSuffixTransportedPrefixPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceChartFrontierBoundaryPackages.rowExhaustedSourceSuffix`

## Claim

In the displayed Case 2 row-exhausted branch, the source-chart boundary can be
packaged with the actual source suffix and finite residual-center
principalization.  The terminal side is transported prefix rows followed by
`sourceSuffixProduct`.

## Proved

Lean combines:

- the existing source-suffix row-exhausted entry-ideal equality;
- the finite center facts for the displayed source-coordinate chart map:
  pivot value membership, divisibility by `u`, and center ideal
  `Ideal.span {u}`;
- a new source-suffix payload field in the frontier package.

## Assumed

The common displayed Case 2 source-chart hypotheses remain explicit: pre
exponent certificates, level invariants, least-value gap, residual chart-family
boundary, row exhaustion `prefixMinNat n S=J+1`, and the supplied source suffix
data.

## Deferred

Original-row equality, terminal-last suffix identity, `(S+1,0)` relabelled
level/exponent data for the row-exhausted wide-next branch, chart construction,
chart coverage, source production, transition invariance, Jacobian arithmetic,
normal crossings, pole order, and RLCT extraction.

## Review

- xhigh A4 scout `Sartre` proposed this slice and checked the transported-row
  source-suffix algebra.
- Focused Lean build passed for `DLNFibre.DLN.Aoyagi.BlowupArithmetic`.
- Independent xhigh reviewer `Aquinas` found no fidelity or overclaiming
  issues and recommended banking.
