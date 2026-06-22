# Reproduction - Case 2 obligation row-exhausted Cterm frontier

Date: 2026-06-22.

Status: finite projection from a supplied source-production obligation.

## Source Anchor

Aoyagi PDF pp. 21-22, Case 2.  In the row-exhausted stopped branch the
terminal side is the stopped terminal prefix multiplied by the remaining
source suffix.  The currently proved boundary writes that terminal prefix with
the transported rows of `Q^-1 C`.

This slice does not add source evidence.  It only consumes a supplied
`SourceProductionObligation`.

## Finite Calculation

The row-exhausted frontier field of the obligation supplies the source-suffix
payload with terminal prefix factor

```text
transportedRows(C).submatrix terminalPrefixRows id.
```

The same obligation supplies the row-exhausted terminal-row equality

```text
Cterm = transportedRows(C).
```

Therefore the terminal prefix factor can be rewritten as

```text
Cterm.submatrix terminalPrefixRows id.
```

The old-side matrix, the source suffix `sourceSuffixProduct`, and the finite
center facts are unchanged.

## Lean Names

```text
RowExhaustedSourceSuffixSuppliedCtermPrefixPayload
SourceProductionObligation.rowExhausted_frontier_suppliedCtermPrefix
```

## Nonclaims

This projection does not construct the obligation, `Cterm`, `Csucc`,
`C'^(S+1)`, a source suffix, a successor chart family, chart coverage,
transition regularity, coordinate post-data, Jacobian arithmetic, normal
crossings, pole order, termination, RLCT extraction, or repair of the printed
Case 2 vector mismatch.

It does not derive the row-exhausted branch hypothesis and does not identify
the transported pivot row with the old source row of `C`.
