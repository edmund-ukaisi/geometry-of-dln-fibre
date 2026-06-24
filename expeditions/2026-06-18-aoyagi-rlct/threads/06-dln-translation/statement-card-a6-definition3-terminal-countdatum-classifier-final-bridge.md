# Statement Card - Definition 3 terminal counted-datum classifier final bridge

## Lean targets

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`
- Reproduction:
  `threads/06-dln-translation/reproduction-definition3-terminal-countdatum-classifier-final-bridge-a6.md`

## Claim

Definition 3 source data plus source-range rank-width hypotheses produce the
selected-width family and ceiling datum used by the final Theorem 2 socket.  If
the produced data are equipped with a supplied terminal counted-datum
classifier, supplied branch-label injectivity, supplied active-ratio
certificates, supplied displayed-ratio chart counts, and the existing A0
extraction hypothesis, then Lean constructs the supplied final boundary.  The
chart-certificate theorem states the same handoff for a supplied
`AoyagiNormalCrossingChartCertificate`.

## Scope

This is finite final-socket plumbing.  It packages already-existing A5 counted
datum classifier APIs into the Definition 3 source-data handoff.  It does not
construct the classifier, prove branch-label injectivity, prove chart counts,
construct normal-crossing charts, or prove pole-order/RLCT consequences
independently of the existing cited A0 boundary.

## Verification

Focused Lean check passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
```

Review:
`threads/06-dln-translation/review-definition3-terminal-countdatum-classifier-final-bridge-a6.md`.
