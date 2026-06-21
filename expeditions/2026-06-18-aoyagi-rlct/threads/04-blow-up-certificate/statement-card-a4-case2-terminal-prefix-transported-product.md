# Statement card - A4 Case 2 terminal-prefix transported product

## Lean Name

- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_transportedRowsPrefix_mul`

## Claim

The stopped Case 2 terminal-prefix product candidate rewrites as

```text
(terminalPrefixWeight * transportedRows|terminalPrefixRows) * F.
```

The terminal rows are the transported rows: old source rows plus the
transported pivot row from `Q^{-1}C`.

## Proved

Lean combines:

- the existing product rewrite through `terminalPrefixCprimeCandidate`;
- the existing identity between that candidate and transported rows.

## Assumed

The stopped-prefix hypothesis, the displayed pivot-continuation hypothesis,
and the supplied following factor `F` are explicit inputs.

## Deferred

Original-row identification without actual-width exhaustion, chart production
of `F` or `C'^(S+1)`, recurrence/exponent post-data production, successor
chart family, chart coverage, transition invariance, Jacobian arithmetic,
normal crossings, pole order, and RLCT extraction.

## Review

- xhigh A4 source scout `Dalton` found no additional source-backed
  chart-production bridge below the current supplied-boundary interface.
- xhigh Lean API scout `Locke` proposed this transported-row product rewrite.
- Focused Lean check passed for `BlowupArithmetic.lean`.
- Independent xhigh reviewer `Averroes` found no blocking issue and confirmed
  the theorem remains finite terminal-prefix algebra.
