# Review - Definition 3 terminal counted-datum classifier final bridge

Reviewer: xhigh `Faraday the 3rd`.

Status: passed after naming/scope corrections.

## Findings

No mathematical blocker was found.  The proposed wrapper is the existing finite
handoff one level higher:

- `TC.TerminalMinimumCountDatumClassifier` supplies only
  `TC.terminalMinimumLabels.card <= data.theorem2OrderFormula`.
- `Set.InjOn TC.branchLabel TC.fullBranches` supplies the remaining finite
  cardinal squeeze to the exact terminal-count formula.
- The existing active-pair/displayed-ratio chart-count classifier bridge builds
  the finite exponent formula.
- The existing Definition 3 source-data wrappers produce `m,data` from source
  data plus rank-width hypotheses.

The reviewer recommended using the name fragment
`terminalMinimumCountDatumClassifier`, matching the Lean type, rather than
`terminalCountDatumClassifier`.

## Scope Check

The theorem must stay in `Theorem2TerminalOrderBridge.lean` under
`AoyagiDefinition3SourceData`; it should not be routed through the stronger
Eq5 endpoint-payload bridge.  Pair-form projection wrappers are unnecessary
because the final-boundary object already carries the existing projections.

The review also corrected the nonclaim wording: the theorem conditionally
packages a final boundary from which the existing A0 projection gives a pole
order formula, so the precise nonclaim is that no pole-order/RLCT consequence
is proved independently of the supplied A0 extraction hypothesis.

## Verification

Focused Lean check passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
```
