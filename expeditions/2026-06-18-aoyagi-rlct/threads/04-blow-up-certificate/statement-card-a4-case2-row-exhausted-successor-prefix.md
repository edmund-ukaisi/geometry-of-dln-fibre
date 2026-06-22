# Statement Card - A4 Case 2 Row-Exhausted Successor-Prefix Rows

## Lean Names

- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTerminalCprimePrefixCandidate_eq_originalRows_successorFollowingFactor`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_rowExhausted_sourceSuffixSuccFollowingPrefixBoundary_withFiniteCenterIdeal`

## Claim

In the displayed Case 2 row-exhausted stopped branch, the existing
source-suffix terminal boundary can be stated with the stopped terminal prefix
rows written as original rows of the formula-level successor following factor
`Csucc`.

## Proved

Lean proves a terminal-prefix row equality:

```text
terminal C' prefix candidate =
  originalRows(Csucc) restricted to the terminal prefix rows.
```

It then rewrites the existing row-exhausted source-suffix boundary through that
row equality and keeps the same finite center principalization facts.

## Assumed

The common displayed Case 2 source-chart hypotheses remain explicit: pre
exponent certificates, level invariants, least-value gap, residual chart-family
boundary, row exhaustion `prefixMinNat n S=J+1`, and supplied source suffix
data.

## Deferred

Source production of `Csucc`, source production of the suffix, full
`C'^(S+1)` chart production, actual-width original-row collapse,
terminal-last suffix identity, `(S+1,0)` relabelled certificates for the
row-exhausted wide-next branch, transition invariance, Jacobian arithmetic,
normal crossings, pole order, termination, and RLCT extraction.

## Review

- Pen-and-paper scout `Anscombe` recommended this exact row-presentation
  boundary.
- Lean/API scout `Kuhn` recommended the same small terminal-prefix companion
  and warned against adding a frontier-package field.
- Focused Lean check passed for `DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
  the module build, full `DLNFibre` build, `scripts/sorries`, and
  `git diff --check` also passed.
- Independent xhigh reviewer `Erdos` found no fidelity or overclaiming issues
  and recommended banking.
