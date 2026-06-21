# Statement card - A4 Case 2 source-chart frontier packages

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.ContinuingSourceChartFrontierPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.ContinuingWeightedSourceFollowingFrontierPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.ActualWidthSourceChartFrontierPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedTerminalLastSourceChartFrontierPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedSourceSuffixTransportedPrefixPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceChartFrontierBoundaryPackages`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_frontierBoundaryPackages`

## Statement

Lean packages the displayed Case 2 source-chart frontier as branch-specific
implications.  A package contains:

- a finite frontier branch witness;
- a continuing consequence under `J+2 <= prefixMinNat n (S+1)`;
- a continuing weighted source-following consequence under
  `J+2 <= prefixMinNat n (S+1)`;
- an actual-width stopped consequence under `n(S+1)=J+1`;
- a row-exhausted terminal-last consequence under `prefixMinNat n S=J+1` and
  `S+1=L`.
- a row-exhausted source-suffix consequence under `prefixMinNat n S=J+1`,
  keeping `sourceSuffixProduct` explicitly and not requiring `S+1=L`.

The branch consequences remain separate because their conclusions have
different domains and different mathematical meaning.

## Proved

- Existing continuing, actual-width, and row-exhausted boundary theorems can be
  assembled behind one fielded implication interface.
- The continuing weighted field keeps the paper-`C'` handoff lower-row only,
  keeps the successor diagonal explicit, and adds finite center
  principalization.
- The actual-width field keeps original source rows and `(S+1,0)` relabelled
  level/exponent certificates.
- The row-exhausted field keeps transported prefix rows and does not relabel.
- The row-exhausted source-suffix field keeps transported prefix rows followed
  by the actual source suffix product.

## Assumed

- Common supplied displayed source-chart hypotheses.
- Explicit branch hypotheses for each field.
- A supplied following matrix in the actual-width field.
- Terminal-last data in the row-exhausted field.
- Fintype/decidable index data for the row-exhausted source-suffix field.

## Cited

- None in Lean.  This is finite matrix/bookkeeping assembly from existing
  theorems.

## Deferred

- Chart construction, chart coverage, successor chart-family data,
  source-produced post-data, transition invariance, termination, Jacobian
  arithmetic, normal crossings, pole order, and RLCT extraction.

## Review

- xhigh API scout `Locke` recommended a fielded implication package rather
  than a single `Or`, because the branch conclusions have incompatible domains.
- xhigh hardener `Boyle` warned not to use a chosen branch witness to drive
  terminal conclusions and not to fold terminal-last into the actual-width
  arbitrary-suffix field.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
