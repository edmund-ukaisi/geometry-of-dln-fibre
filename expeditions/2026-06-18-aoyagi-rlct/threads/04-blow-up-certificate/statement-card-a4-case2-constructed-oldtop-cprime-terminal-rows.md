# Statement card - A4 Case 2 constructed old-top `Cprime` terminal rows

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_oldRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_pivotRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_submatrix_terminalRowEquiv`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_constructedWithOldTopFromCprime_submatrix_terminalRowEquiv`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductReindexedCandidate_constructedWithOldTopFromCprime_eq_weight_mul_terminalStack_mul`

## Claim

Lean now specializes the existing Case 2 terminal transported-row and
terminal-candidate APIs to the constructed old-top/free-`Cprime` source
following factor.

For

```text
C =
  case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
    n hS hcont residual Cold Cprime,
```

the transported terminal rows, reindexed by `case2SourceTerminalRowEquiv J`,
are

```text
verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime).
```

The corresponding source-row terminal candidate has the same reindexed block
presentation, and the explicit source-row matrix

```text
(verticalBlock Cold (case2DisplayedFreeCprimeTop n hS hcont Cprime)).submatrix
  (case2SourceTerminalRowEquiv J).symm id
```

supplies a `SuppliedTerminalCprimeBridge` for the constructed source following
factor.  The stopped source-row terminal product candidate rewrites to

```text
(case2DisplayedSourceTerminalWeight Wold b0 * explicitTerminalRows) * F.
```

## Proved

- Old terminal transported rows of the constructed factor are exactly the
  supplied old-top rows `Cold`.
- The surviving pivot terminal row is the top row of the free displayed
  `Cprime`.
- Reindexing by `case2SourceTerminalRowEquiv J` gives the stacked block
  `[Cold; top(Cprime)]`.
- The same block supplies a terminal `Cprime` bridge with a terminal source-row
  matrix.
- The stopped terminal product candidate can consume that bridge.

## Assumed

Only the finite displayed Case 2 formation hypotheses and arbitrary matrices
`Cold`, `Cprime`, and `F`.  No stopped hypothesis or actual-width hypothesis is
needed for this row presentation.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 21-22, especially
`C'_J^(S+1)=Q^-1 C_J^(S+1)` and the stopped terminal product row order.

## Not Proved

No source-produced `C'^(S+1)`, terminal chart construction, chart coverage,
transition regularity, source suffix production, coordinate-derived post-data,
Jacobian/volume-form theorem, normal crossings, pole order, termination, RLCT,
or repair of the printed Case 2 vector mismatch.

## Reproduction and Review

- Reproduction:
  `reproduction-case2-constructed-oldtop-cprime-terminal-rows-a4.md`.
- Review:
  `review-case2-constructed-oldtop-cprime-terminal-rows-a4.md`.

## Verification

- From `lean/`: `scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- From `lean/`: `scripts/lb DLNFibre`
- From `lean/`: `scripts/sorries`
- From repo root: `git diff --check`
