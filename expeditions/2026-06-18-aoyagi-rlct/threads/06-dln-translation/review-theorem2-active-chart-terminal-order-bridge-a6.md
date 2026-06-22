# Review - Theorem 2 active chart-terminal-order bridge

Date: 2026-06-22.

Reviewer: xhigh API scout `Gauss the 2nd`.

## Verdict

Pass, after naming adjustment.

## Findings

No blocking findings.

## Naming Adjustment

The reviewer recommended renaming the initial `chartTerminalLabels` names to
the more explicit `chartCount_terminalMinimumLabels_card`, because the
certificate is a chart-count maximum certificate whose candidate value is the
terminal-minimum label count.  The Lean names and statement-card entries were
updated accordingly.

## Scope Check

The bridge replaces the raw equality

```text
D.exponentOrder = TC.terminalMinimumLabels.card
```

by the finite maximum certificate:

```text
D.minCountInChart c = TC.terminalMinimumLabels.card
forall c', D.minCountInChart c' <= TC.terminalMinimumLabels.card
```

It still does not claim chart production, source-backed chart counts,
terminal-label production, Lemma 5 no-extra coverage, pole order without A0,
normal crossings, or RLCT extraction.

## Risk Noted

`D.minCountInChart` counts coordinates attaining the actual
`D.exponentMinimum`.  If later source-facing chart counts are phrased as
coordinates attaining the displayed Theorem 2 lambda value instead, an
additional rewrite bridge from the active-ratio minimum certificate to
`D.exponentMinimum` may be needed.

## Checks

Reviewer check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
```

Controller checks after incorporating the naming adjustment:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderBridge
```
