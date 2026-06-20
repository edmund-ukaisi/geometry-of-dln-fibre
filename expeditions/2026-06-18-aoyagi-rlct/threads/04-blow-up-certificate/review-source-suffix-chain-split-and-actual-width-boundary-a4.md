# Review - A4 source suffix split and actual-width terminal boundary

Reviewed objects:

- `DLNFibre.DLN.Aoyagi.paperMatrixChain_trans`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsBoundary`

Verdict: no blocking source/math or Lean API issue found.

The raw chain split has the correct Aoyagi paper-order orientation:

```text
paperMatrixChain(i,j) = paperMatrixChain(i,m) * paperMatrixChain(m,j).
```

This matches `paperMatrixChain_succ_right`, where extending the upper endpoint
right-multiplies by the next edge.

The actual-width terminal boundary does not overclaim source production.  Its
terminal matrix is explicitly `case2DisplayedSourceTerminalOriginalRows C`,
and `C`, `Ctail`, and `chartFamily` remain supplied.  The actual-width
hypothesis `n(S+1)=J+1` is used only to identify the transported pivot row with
the original source row and to allow the `(S+1,0)` relabelled level/exponent
domain projections.

## Caveats

- The terminal boundary is actual-width only; it is not a row-exhausted
  wide-next theorem.
- It still has an existential row-operation witness `q`.
- Relabelled `(S+1,0)` data cover level invariants and exponent-domain
  certificates only; no automatic Case 2 gap/tail transport is proved.
- No source-produced `C'^(S+1)`, chart coverage, chart-produced post-data,
  Jacobian, normal-crossing/RLCT, termination, transition invariance, or
  printed-vector repair is proved.
- `paperMatrixChain_trans` is raw chain algebra only; source-suffix empty and
  peel wrappers remain future work.
