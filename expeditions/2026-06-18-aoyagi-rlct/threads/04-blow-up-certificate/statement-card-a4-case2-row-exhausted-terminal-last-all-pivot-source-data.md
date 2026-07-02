# Statement card - A4 Case 2 row-exhausted terminal-last all-pivot source data

Status: Lean implemented after pen-and-paper reproduction.

Reproduction:
`reproduction-a4-case2-row-exhausted-terminal-last-all-pivot-source-data.md`.

Review:
`review-a4-case2-row-exhausted-terminal-last-all-pivot-source-data.md`.

## Target

Expose the existing displayed Case 2 terminal-last row-exhausted frontier
payload in the all-pivot finite source-data layer, separate from the
source-suffix row-exhausted record.

## Lean Surface

```text
case2AllPivotRowExhaustedTerminalLastGuard
case2AllPivotRowExhaustedStoppedGuard_of_terminalLastGuard

Case2AllPivotRowExhaustedTerminalLastProducedSourceData
Case2AllPivotRowExhaustedTerminalLastProducedSourceData.of_sourceInput
```

## Source Boundary

Aoyagi pp. 19-22 support the displayed Case 2 row-exhausted terminal
calculation.  The Lean record only packages the already-formalized
terminal-last transported-prefix frontier payload under the stronger guard
`active row-exhausted and S + 1 = L`.

## Nonclaims

No analytic producer payload, full row-exhausted semantic payload, branch-data
record, chart production, source-domain witness, center alignment,
generic-`alpha` transport, normal crossing, pole order, or RLCT extraction is
proved by this card.
