# Statement card - A4 Case 2 source-production obligation row-exhausted Csucc

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.rowExhausted_Cterm_eq_originalRows_Csucc`

## Statement

For a supplied Case 2 source-production obligation, the row-exhausted terminal
matrix `Cterm` can be rewritten as the original terminal rows of the supplied
successor following factor `Csucc`.

## Proved

Under `hrow : prefixMinNat n S = J+1`, the obligation supplies
`Cterm = transportedRows(C)`.  The existing finite row identity identifies
`transportedRows(C)` with `originalRows` of the canonical formula-level
successor factor.  The supplied equality `Csucc_eq_formula` then rewrites the
canonical factor to the obligation's supplied `Csucc`.

## Assumed

An inhabitant of `SourceProductionObligation`, including its supplied formula
equality for `Csucc`, and the row-exhausted branch hypothesis `hrow`.

## Cited

None.  This is finite matrix-row rewriting.

## Deferred

Constructing the obligation, source production of `Csucc` or `C'^(S+1)`,
suffix production, successor chart-family construction, chart coverage,
transition regularity, coordinate derivation of corrected post-data, Jacobian
arithmetic, normal crossings, pole order, termination, and RLCT extraction.

## Review

Xhigh scout `Herschel` recommended this exact projection and warned not to
derive `hrow`, make stopped branches exclusive, or identify row `J+1` with the
old source row `C(J+1,-)`.  Xhigh reviewer `Gibbs` passed the implemented
diff with no findings.

## Verification

Focused Lean, module build, full build, sorry scan, and diff check pass:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.
