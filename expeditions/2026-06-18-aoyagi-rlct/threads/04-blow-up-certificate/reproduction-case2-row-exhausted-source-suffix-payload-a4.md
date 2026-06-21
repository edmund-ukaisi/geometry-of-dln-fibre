# Reproduction - A4 Case 2 Row-Exhausted Source-Suffix Payload

Status: reproduced; Lean checked; xhigh review pending.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  In the row-exhausted stopped branch

```text
prefixMinNat n S = J+1,
```

the current source-prefix rows are exhausted, but this does not imply actual
next-width exhaustion `n(S+1)=J+1` and does not imply `S+1=L`.  The terminal
matrix on the stopped side must therefore keep the transported top row of
`Q^{-1}C` and, away from terminal-last, must keep the remaining source suffix
product.

## Calculation

The already-proved source-suffix row-exhausted theorem gives

```text
matrixEntryIdeal(old weighted top/source block * sourceSuffixProduct)
  =
matrixEntryIdeal(transportedPrefixProduct * sourceSuffixProduct).
```

Here the right-hand transported-prefix product is

```text
case2DisplayedSourceTerminalWeightPrefixCandidate
  * transportedRowsPrefix
```

where `transportedRowsPrefix` is the prefix restriction of
`case2DisplayedSourceTerminalTransportedRows`.  The final row is still the top
row of `Q^{-1}C`; no original-row equality is used.

Independently, the displayed source-coordinate chart map satisfies the finite
center facts:

```text
u is one of the transformed center values,
every transformed center value is divisible by u,
the transformed finite center ideal is Ideal.span {u}.
```

The new package is just the conjunction of these facts:

```text
sourceChart_rowExhausted_sourceSuffixTransportedPrefixBoundary_withFiniteCenterIdeal
```

It has no terminal-last hypothesis.  The suffix remains
`sourceSuffixProduct κ Ctail S hSuffix`.

## Frontier Package Update

The fielded frontier package now also exposes this non-terminal row-exhausted
payload:

```text
RowExhaustedSourceSuffixTransportedPrefixPayload
SourceChartFrontierBoundaryPackages.rowExhaustedSourceSuffix
```

This does not replace the older terminal-last row-exhausted field.  The
terminal-last field remains useful when the suffix is known to be the identity.

## Nonclaims

- No replacement of transported rows by original rows.
- No terminal-last simplification or identity suffix unless separately
  supplied.
- No `(S+1,0)` relabelled level or exponent certificate in the row-exhausted
  wide-next branch.
- No chart construction, chart coverage, source-produced `C'^(S+1)`,
  transition invariant, Jacobian arithmetic, normal crossings, pole order, or
  RLCT extraction.
