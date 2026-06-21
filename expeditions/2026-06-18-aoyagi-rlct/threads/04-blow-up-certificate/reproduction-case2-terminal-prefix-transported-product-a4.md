# Reproduction - Case 2 terminal-prefix transported product

Status: reproduced; Lean checked; independent xhigh review survived.

## Source

Aoyagi PDF pp. 19-22 supports the local displayed Case 2 algebra: the pivot
chart, the transported following factor `C' = Q^{-1}C`, the stopped terminal
display, and the terminal-prefix row presentation.  The source does not
construct the successor chart family or prove that a full next following matrix
is chart-produced.

This slice only rewrites the already named terminal-prefix product candidate
using the explicit transported terminal rows.

## Calculation

The existing source-row terminal product candidate satisfies

```text
terminalPrefixProduct =
  (terminalPrefixWeight * terminalPrefixCprimeCandidate) * F.
```

The existing transported-row identity says

```text
terminalPrefixCprimeCandidate =
  transportedTerminalRows restricted to the terminal-prefix row index.
```

Substitution gives

```text
terminalPrefixProduct =
  (terminalPrefixWeight *
    transportedTerminalRows|terminalPrefixRows) * F.
```

The last row is the transported top row of `Q^{-1}C`.  It is not replaced by
the original source row unless the actual-width column-exhaustion hypothesis
`n(S+1)=J+1` is separately available.

## Lean Target

```text
case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_transportedRowsPrefix_mul
```

## Kill Conditions

- Do not replace transported rows by original rows without
  `n(S+1)=J+1`.
- Do not drop the stopped-prefix hypothesis
  `¬ J+2 <= prefixMinNat n (S+1)`.
- Do not treat the supplied following factor `F` as chart-produced.
- Do not infer recurrence/exponent post-data, successor chart family, chart
  coverage, transition invariance, Jacobian, normal crossings, pole order, or
  RLCT extraction.

## Nonclaims

No chart is constructed, no successor `C'^(S+1)` is source-produced, no
post-data or transition invariant is proved, and no normal-crossing/RLCT
consequence is extracted.
