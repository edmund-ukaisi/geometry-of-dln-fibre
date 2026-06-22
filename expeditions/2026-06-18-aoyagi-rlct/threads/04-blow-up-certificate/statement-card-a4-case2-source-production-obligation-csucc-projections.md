# Statement card - A4 Case 2 source-production obligation Csucc projections

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_Csucc_tail_eq_original`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.actualWidth_Cterm_eq_originalRows_Csucc`

## Statement

For a supplied Case 2 source-production obligation:

- the supplied successor following factor `Csucc` has the same next same-stage
  tail as the old source following factor `C`;
- in the actual-width stopped branch `n(S+1)=J+1`, the terminal matrix
  `Cterm` can be rewritten as the original terminal rows of `Csucc`.

## Proved

Both projections use the supplied formula equality `Csucc_eq_formula`.

The continuing-tail projection applies the existing theorem that the
`(S,J+1)` following-factor restriction ignores the replaced row `J+1`.

The actual-width terminal-row projection uses the obligation field
`Cterm = originalRows(C)`, the existing actual-width collapse
`case2DisplayedSourceSuccessorFollowingFactor = C`, and `Csucc_eq_formula`.

## Assumed

An inhabitant of `SourceProductionObligation`, including its supplied formula
equality for `Csucc`.  The actual-width projection additionally assumes the
stopped branch hypothesis `hwidth : n(S+1)=J+1`.

## Cited

None.  These are finite matrix-row and row-tail rewrites.

## Deferred

Constructing the obligation, source production of `Csucc` or `C'^(S+1)`,
suffix production, successor chart-family construction, chart coverage,
transition regularity, coordinate derivation of corrected post-data, Jacobian
arithmetic, normal crossings, pole order, termination, and RLCT extraction.

## Review

Xhigh reviewer Hilbert the 2nd passed the slice after one documentation
precision fix: the actual-width projection consumes the supplied
`actualWidth_Cterm_eq` branch field as well as the actual-width collapse and
`Csucc_eq_formula`.

## Verification

Focused Lean, aggregate build, sorry scan, and diff check pass:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.
