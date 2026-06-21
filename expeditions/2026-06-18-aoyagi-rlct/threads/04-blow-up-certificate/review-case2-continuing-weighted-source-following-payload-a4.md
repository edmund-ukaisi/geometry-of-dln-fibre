# Review - A4 Case 2 Continuing Weighted Source-Following Payload

Reviewer: xhigh independent reviewer `Boyle`.

## Verdict

No formalisation or math findings.  Bank as-is after the documentation updates.

## Checks

- The theorem
  `sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal`
  packages only next residual-center nonemptiness, the existing weighted
  lower-row handoff, corrected local post certificates already present in that
  handoff, and finite residual-center membership/divisibility/principalization.
- `ContinuingWeightedSourceFollowingFrontierPayload` matches the theorem
  conclusion and does not add stronger semantic content.
- `SourceChartFrontierBoundaryPackages.continuingWeighted` is wired directly
  to the new theorem under the explicit next-continuation guard.

## Nonclaims Checked

The Lean statement and local comments do not claim full chart production, chart
coverage, source-produced `C'` post-data, transition invariance, Jacobian
arithmetic, normal crossings, pole order, RLCT, or a pivot-row product.

## Documentation Follow-Up

The reviewer noted that the frontier statement card and theorem ledger needed
to mention the new `ContinuingWeightedSourceFollowingFrontierPayload` and
`continuingWeighted` field.  The controller patch for this slice updates those
files and records a dedicated reproduction/statement card.

## Verification

The reviewer ran:

```text
git diff --check -- lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

Both passed.
