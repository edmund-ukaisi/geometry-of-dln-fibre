# Review - A2 source-rank-stratum Theorem 3 boundary

Date: 2026-06-23.

Reviewer: xhigh read-only scout `Carson`.

## Verdict

Pass at the fixed-base/source-rank-stratum wrapper scope.

The slice safely combines two already-proved elementary pieces:

- the triangular endpoint form with lower-right block equal to
  `ChartLocalSuffixState.residualProduct`;
- the source-stratum residual block ranks `rEdge p - r`.

No source or math error was found that invalidates the Lean target. The
nonclaims correctly exclude exact-rank openness, Aoyagi Lemma 1 normalization,
analytic ideal transport, regular-coordinate RLCT additivity, normal crossings,
pole order, and final RLCT extraction.

## Caveats to Preserve

- The phrase "source rank stratum" is repository terminology. Aoyagi fixes
  nearby layer ranks, but does not define this stratum as a named object.
- Source-rank-stratum membership supplies the rank data for the subtraction
  formula only. The regular-corner determinant-chart hypotheses required by
  Lemma 2 are carried by the fixed-base product-reduction certificate.
- `ChartLocalSuffixState.residualProduct` is the canonical Lean orientation and
  order. Do not rewrite it as a paper-order product without a separate
  orientation bridge.
- Relative `nhdsWithin` wrappers are not nonemptiness, openness, or base-rank
  evidence.
- Lean uses natural subtraction `rEdge p - r`. The source inequality
  `r <= rEdge p` is recorded in the stratum and should be carried explicitly
  by downstream arithmetic even where the current proof does not consume it.

## Result

Proceed with the Lean wrapper under the names
`PaperEndpointFixedBaseTriangularResidualProductSourceRanks` and
`PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks`.
