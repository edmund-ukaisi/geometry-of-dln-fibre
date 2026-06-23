# Review - A4 Case 2 selected-entry chart-family data

Date: 2026-06-23.

Verdict: PASS, with one source caveat recorded.

Reviewers:

- source/math fidelity: `Dalton the 2nd`, xhigh;
- Lean/API: `Sagan the 2nd`, xhigh.

## Source/Math Findings

The selected-entry chart-family data are source-faithful inside the stated
finite-coordinate boundary.  `SelectedEntryChartFamilyData` records the
elementary affine chart formula: the pivot value is `u`, and every non-pivot
center value is `u * residual`.

The Case 2 specialization is also source-faithful for Aoyagi pp. 19-20.  The
finite center is the residual block, and the displayed pivot is the top-left
entry `(J+1,J+1)` under the continuation hypothesis.

The adapter
`Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_displayedPivot_eq_sourceChartMap`
is only a definitional equality between the standard selected-entry chart
family and the existing displayed source chart map.  It introduces no new
source claim.

The theorem
`sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData` is supported
by the displayed Case 2 algebra on Aoyagi pp. 20-21: selected-entry
substitution, the regular `Q` operation, `C' = Q^-1 C`, the regular `P`
operation, `D''' = blockdiag(1,D_{J+1})`, and finite reindexing to the next
same-stage source-product shape.

## Required Caveat

Aoyagi p. 20 defines `b'_i = u_{S,J+1} b_i`, but p. 21 later displays an
additional outside factor `u_{S,J+1} diag(b') ...`.  These two printed lines
are not simultaneously literal.

The Lean theorem follows the corrected concrete post-data convention
`post.weight = u * pre.weight`.  It formalises the corrected displayed
algebra, not the inconsistent literal printed product with a second outside
factor of `u`.

## Lean/API Findings

No blocking Lean/API issue was found.  The statement remains finite matrix
algebra plus corrected post-data, and does not assert chart production,
coverage, transition regularity, Jacobian arithmetic, normal crossings, pole
order, or RLCT content.

The displayed pivot is non-vacuously backed by `hS` and `hcont`.

Minor nonblocking API note: the simp lemmas
`Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_displayedPivot`
and
`Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_displayedPivot_eq_sourceChartMap`
have overlapping left-hand sides with definitionally equal right-hand sides.
This is acceptable in the current slice.  If simp normal forms become unstable,
demote one of them to a non-simp adapter.

## Checks

Reviewers and controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.
