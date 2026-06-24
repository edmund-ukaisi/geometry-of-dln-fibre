# Review - Case 2 constructed old-top `Cprime` terminal rows

Date: 2026-06-24.

Reviewer: xhigh pen-and-paper checker `Hooke the 2nd`, with Lean API scout
`Turing the 2nd`.

## Verdict

Accept after corrections.  The corrections were incorporated before Lean work.

The finite-row claim is sound: for

```text
C =
  case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
    n hS hcont residual Cold Cprime,
```

the transported terminal source rows are the old rows from `Cold` plus the
surviving pivot/top row of the free `Cprime`.

## Source and Scope Check

Aoyagi supports the row shape through the displayed Case 2 formula
`C'_J^(S+1)=Q^-1 C_J^(S+1)` on p. 21, the stopped branch where `D'''_J` is a
one-row or one-column terminal block on pp. 21-22, and the p. 22 terminal
product restacking as old rows plus the surviving transformed row in
`C'^(S+1)`.

Aoyagi does not state the arbitrary free-`Cprime` constructor.  The accepted
Lean target is therefore repo finite bookkeeping motivated by the display, not
a source theorem producing arbitrary terminal chart coordinates.

## Required Corrections Applied

- The reproduction now states the exact Lean types for `Cold` and `Cprime`.
- The reindexed terminal-row formula is explicit:

```text
(transportedRows C).submatrix (case2SourceTerminalRowEquiv J) id
  =
verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime).
```

- The supplied bridge constructor uses a terminal source-row matrix

```text
(verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime)).submatrix
  (case2SourceTerminalRowEquiv J).symm id.
```

- The kill condition now distinguishes terminal rows from source-current rows:
`[Cold; Cprime]` is wrong for the terminal-row theorem, but correct for the
source-current/successor block under `case2SourceOldTopPaperCprimeRowEquiv`.
- The terminal-row count boundary is recorded: `case2SourceTerminalRowIndex J`
is `Icc 1 (J+1)`, and identifying it with the terminal prefix row range needs
a separate stopped hypothesis.

## Lean API Check

The API scout confirmed that the terminal APIs live inside
`DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary`, while the
source row/equivalence and constructed/free-`Cprime` APIs are top-level under
`DLNFibre.DLN.Aoyagi`.

The weakest useful statements were the transported-row reindex theorem, the
terminal-candidate reindex theorem, an explicit `SuppliedTerminalCprimeBridge`
constructor with the old-top-plus-free-top terminal matrix, and the product
rewrite consuming that bridge.

## Nonclaims

This review accepts only finite row transport/bookkeeping.  It does not accept
source production of `C'^(S+1)`, terminal chart construction, chart coverage,
transition regularity, source suffix production, coordinate-derived post-data,
normal crossings, pole order, termination, RLCT extraction, or repair of the
printed Case 2 vector mismatch.
