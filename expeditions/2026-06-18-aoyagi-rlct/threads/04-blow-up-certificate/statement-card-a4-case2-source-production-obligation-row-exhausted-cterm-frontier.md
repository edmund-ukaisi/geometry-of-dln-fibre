# Statement card - A4 Case 2 source-production obligation row-exhausted Cterm frontier

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedSourceSuffixSuppliedCtermPrefixPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.rowExhausted_frontier_suppliedCtermPrefix`

## Statement

For a supplied Case 2 source-production obligation, the row-exhausted
source-suffix frontier can be restated with the terminal prefix factor written
as the supplied terminal matrix `Cterm`, restricted to the terminal prefix
rows.

## Proved

Under `hrow : prefixMinNat n S = J+1`, the obligation supplies the existing
row-exhausted source-suffix payload and the equality
`Cterm = transportedRows(C)`.  Rewriting the terminal prefix factor by that
equality gives the supplied-`Cterm` payload.  The finite center membership,
divisibility, and principalization facts are unchanged.

## Assumed

An inhabitant of `SourceProductionObligation`, including its supplied
row-exhausted frontier payload and terminal-row equality, plus the
row-exhausted branch hypothesis `hrow`.

## Cited

None.  This is finite matrix-row rewriting.

## Deferred

Constructing the obligation, source production of `Cterm`, `Csucc`, or
`C'^(S+1)`, suffix production, successor chart-family construction, chart
coverage, transition regularity, coordinate derivation of corrected post-data,
Jacobian arithmetic, normal crossings, pole order, termination, and RLCT
extraction.

## Review

Xhigh Lean/API scout `Lagrange the 2nd` recommended this exact supplied-`Cterm`
projection.  Xhigh post-implementation reviewer `Halley the 2nd` found no
Lean/source-fidelity issue with the theorem and requested stale historical
next-chart-family wording cleanup, which has been applied.

## Verification

Focused Lean and module build passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
```

Full-library build, sorry scan, and final diff check are recorded in the
expedition closeout.
