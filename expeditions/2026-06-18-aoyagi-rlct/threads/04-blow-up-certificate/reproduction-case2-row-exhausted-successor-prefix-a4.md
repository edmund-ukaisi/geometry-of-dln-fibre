# Pen-and-paper reproduction - A4 Case 2 row-exhausted successor-prefix rows

Status: reproduced and formalised; xhigh review pending.

## Source Anchor

Aoyagi PDF pp. 21-22, Case 2 stopped branch.  The source text says that after
the displayed `Q` and `P` row operations, if the next continuation fails then
the terminal display uses a stopped `C'^(S+1)` followed by the remaining
source suffix product.

This checkpoint concerns the row-exhausted stopped subcase

```text
prefixMinNat n S = J+1.
```

It does not assume actual next-width exhaustion `n(S+1)=J+1`.

## Reproduction

The existing row-exhausted source-suffix boundary has terminal side

```text
matrixEntryIdeal
  ((terminalWeightPrefix *
      transportedRows(C).submatrix terminalPrefixRows id) *
    sourceSuffixProduct).
```

Here `transportedRows(C)` has rows `1,...,J+1`: old rows `1,...,J` are
original source rows of `C`, while row `J+1` is the top row of Aoyagi's
transported following factor `Q^-1 C`.

The formula-level successor following factor is

```text
Csucc(j,a) =
  if j = J+1 then top row of (Q^-1 C) at a
  else C(j,a).
```

Therefore the terminal row matrix with transported row `J+1` is exactly

```text
case2DisplayedSourceTerminalOriginalRows Csucc.
```

After reindexing to the terminal prefix rows, the same row-exhausted
source-suffix boundary can be written as

```text
matrixEntryIdeal
  ((terminalWeightPrefix *
      originalRows(Csucc).submatrix terminalPrefixRows id) *
    sourceSuffixProduct).
```

The finite center facts are unchanged: `u` is a transformed center value, every
transformed center value is divisible by `u`, and the transformed center ideal
is `Ideal.span {u}`.

## Lean Names

```text
case2DisplayedSourceTerminalCprimePrefixCandidate_eq_originalRows_successorFollowingFactor
sourceChart_rowExhausted_sourceSuffixSuccFollowingPrefixBoundary_withFiniteCenterIdeal
```

## Boundary Checks

- The suffix remains the actual `sourceSuffixProduct`.
- The row-exhausted hypothesis is `prefixMinNat n S = J+1`; it is not replaced
  by actual next-width exhaustion.
- Row `J+1` is original only as a row of `Csucc`, not as a row of `C`.
- No new `SourceChartFrontierBoundaryPackages` field is introduced.

## Kill Conditions

- Do not identify transported row `J+1` with `C(J+1,-)` without
  `n(S+1)=J+1`.
- Do not add `(S+1,0)` relabelled level/exponent certificates in the
  row-exhausted wide-next branch.
- Do not claim source production of `Csucc`, source production of the suffix,
  chart coverage, transition invariance, normal crossings, pole order,
  termination, RLCT extraction, or repair of the printed Case 2 vector
  mismatch.
