# Reproduction - Case 2 constructed old-top `Cprime` terminal rows

Date: 2026-06-24.

Status: controller reproduction, pending independent check.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2, performs the displayed residual-block pivot
operation and writes on p. 21

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

In the stopped branch on pp. 21-22, the displayed `D'''_J` is a one-row or
one-column terminal block, and on p. 22 the terminal product is restacked in
source row order after the old rows `1,...,J`, followed by the surviving
transformed pivot row in `C'^(S+1)`.  Earlier A4 slices already recorded this
as the finite source-row terminal candidate:

```text
case2DisplayedSourceTerminalCprimeCandidate
```

and its formula-level version with transported rows:

```text
case2DisplayedSourceTerminalTransportedRows.
```

This slice specializes that existing terminal-row presentation to the
constructed old-top/free-`Cprime` source following factor.  It does not assert
that the constructed factor is source-produced by Aoyagi's chart.  Aoyagi does
not state the arbitrary free-`Cprime` constructor; this result is repo finite
bookkeeping motivated by the displayed `Q^-1 C` operation and terminal row
order.

## Data

Fix the displayed Case 2 hypotheses

```text
1 <= S,
J+1 <= prefixMinNat n (S+1).
```

Let

```text
Cold :
  Matrix (case2SourceOldTopRowIndex J) tau R

Cprime :
  Matrix (Unit + pivotComplement (case2DisplayedPivotCol n hS hcont)) tau R
```

The existing constructor

```text
case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
```

builds a total source-coordinate following factor `C` by setting

```text
C(old row i)     = Cold(i),
C(residual cols) = Q*Cprime,
C(other rows)    = 0.
```

The already-proved projection lemmas give

```text
oldTop(C)      = Cold,
paperCprime(C) = Cprime.
```

The second equality is the finite identity `Q^-1*(Q*Cprime)=Cprime`, expressed
through Aoyagi's displayed `paperCprime` operation.

## Terminal Rows

The source-row terminal transported matrix for an arbitrary following factor
`C` is

```text
case2DisplayedSourceTerminalTransportedRows(n,S,J,residual,C)(i,-)
  =
    if i = J+1 then top row of paperCprime(C)
    else C(i,-).
```

For the constructed `C` above:

1. If `i` is an old row in `{1,...,J}`, then `i != J+1`, so the transported
   terminal row is `C(i,-) = Cold(i,-)`.
2. If `i` is the surviving pivot row `J+1`, then the transported terminal row
   is the top row of `paperCprime(C) = Cprime`, namely

```text
case2DisplayedFreeCprimeTop(n,S,J,Cprime).
```

Under the source terminal row equivalence

```text
case2SourceTerminalRowEquiv J :
  case2SourceOldTopRowIndex J + Unit ~= case2SourceTerminalRowIndex J,
```

the constructed terminal rows therefore reindex to

```text
(case2DisplayedSourceTerminalTransportedRows n hS hcont residual C).submatrix
    (case2SourceTerminalRowEquiv J) id
  =
verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime).
```

Equivalently, in source-row indexing,

```text
case2DisplayedSourceTerminalTransportedRows n hS hcont residual C
  =
(verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime)).submatrix
  (case2SourceTerminalRowEquiv J).symm id.
```

The same matrix supplies a `SuppliedTerminalCprimeBridge` for the constructed
source following factor, with terminal source-row matrix

```text
Cterm =
  (verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime)).submatrix
    (case2SourceTerminalRowEquiv J).symm id.
```

## Boundary Cases

- If `J=0`, then `case2SourceOldTopRowIndex J` is empty.  The equivalence sends
  only the `Unit` row to source row `1=J+1`, so the statement reduces to the
  one-row top of `Cprime`.
- The terminal row type is exactly
  `case2SourceTerminalRowIndex J = Finset.Icc 1 (J+1)`, so it has the old `J`
  rows plus one pivot row.  Identifying this with the terminal prefix row range
  requires an additional stopped hypothesis such as
  `not (J+2 <= prefixMinNat n (S+1))`.
- No actual-width hypothesis is used.  In the row-exhausted wide-next case the
  terminal pivot row is transported, not an original source row.
- Under the separate actual-width hypothesis `n(S+1)=J+1`, the existing API
  may collapse the transported pivot row to the original source row, but that
  is not part of this free-`Cprime` specialization.

## Formalisation Target

Useful Lean statements:

```text
case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_oldRow
case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_pivotRow
case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_submatrix_terminalRowEquiv
case2DisplayedSourceTerminalCprimeCandidate_constructedWithOldTopFromCprime_submatrix_terminalRowEquiv
SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime
```

The block equality should use the exact right-hand side

```text
verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime),
```

not `verticalBlock Cold Cprime`, since terminal rows retain only the old rows
and the top row of `Cprime`.

## Kill Conditions

- If the theorem states the terminal matrix as `[Cold; Cprime]`, it is wrong:
  `Cprime` still includes post-pivot lower rows that are not terminal rows.
  The same block `[Cold; Cprime]` is correct only for the source-current or
  successor source-row block under `case2SourceOldTopPaperCprimeRowEquiv`, not
  for terminal rows.
- If old rows are read from the reconstructed residual block `Q*Cprime` rather
  than from `Cold`, the row domains have been confused.
- If the pivot row is replaced by the original source row without the
  actual-width column-exhaustion hypothesis, the row-exhausted wide-next case is
  mishandled.
- If the result is named as source production of `C'^(S+1)`, construction of a
  terminal chart, or construction of a `SourceProductionObligation`, it
  overclaims.

## Nonclaims

This is finite row-index and matrix-bookkeeping only.  It does not construct
source data, terminal chart data, successor chart families, suffixes,
transition regularity, chart coverage, coordinate-derived post-data,
Jacobians, normal crossings, pole order, termination, RLCT extraction, or a
repair of the printed Case 2 vector mismatch.
