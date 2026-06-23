# Statement card - A4 Case 2 selected-entry chart-family data

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `SelectedEntryChartFamilyData`
- `SelectedEntryChartFamilyData.standard`
- `SelectedEntryChartFamilyData.value_pivot`
- `SelectedEntryChartFamilyData.value_of_ne`
- `SelectedEntryChartFamilyData.selected_dvd_value`
- `SelectedEntryChartFamilyData.selected_mem_valueSet`
- `SelectedEntryChartFamilyData.centerIdeal_eq_span_singleton`
- `Case2ResidualBlockSelectedEntryChartFamilyData`
- `Case2ResidualBlockSelectedEntryChartFamilyData.standard`
- `Case2ResidualBlockSelectedEntryChartFamilyData.displayedPivot`
- `Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_displayedPivot`
- `Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_displayedPivot_eq_sourceChartMap`
- `sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData`

## Claim

The finite selected-entry affine chart formula can be packaged as concrete
chart-family data over a finite center.  For Aoyagi Case 2, the displayed
pivot `(J+1,J+1)` specializes this generic selected-entry data to the existing
displayed source chart map.

The displayed source-chart `Q/P` identity can then be combined with the
previous finite next-state source-product reindex to produce the displayed
source-chart product in next same-stage `(S,J+1)` source-product form, together
with the corrected concrete post-data projections already supplied by the
displayed boundary.

## Inputs Kept Explicit

- finite center and selected pivot data;
- for Case 2, `1 <= S` and `J+1 <= prefixMinNat n (S+1)`;
- the supplied displayed Case 2 chart-family boundary;
- pre-state recurrence data, corrected exponent certificates, level
  invariants, and least-value gap hypotheses;
- source following factor `C`;
- formula-level `case2DisplayedSourceSuccessorFollowingFactor`.

## Proved

For selected-entry charts:

```text
pivot value = u,
non-pivot value = u * residual,
u divides every transformed center value,
span(transformed finite-center values) = span({u}).
```

For the displayed Case 2 pivot:

```text
standard selected-entry value at (J+1,J+1)
  = case2DisplayedSourceChartMap.
```

For the source-product bridge, Lean returns a row-operation witness `q` and
proves the displayed source-chart product reindexed to the next `(S,J+1)`
source product, plus corrected post-data certificates for the updated label.

## Not Proved

No chart coverage, transition regularity, all-pivot chart construction, source
production of full `C'^(S+1)`, suffix production, chart-produced corrected
post-data, Jacobian arithmetic, normal crossings, pole order, termination,
RLCT, or repair of the printed Case 2 vector mismatch.

The corrected exponent data are a repaired certificate, not the printed Case 2
vector on Aoyagi p. 20.  The weight update also follows the corrected
post-state convention `post.weight = u * pre.weight`; it is not the literal
combination of Aoyagi's printed `b'_i = u b_i` line with the later additional
outside `u` factor.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

## Review

Xhigh source reviewer `Dalton the 2nd` passed the slice, with the required
weight-factor caveat above.  Xhigh Lean/API reviewer `Sagan the 2nd` passed
the slice and noted only a nonblocking future simp-normal-form risk from two
definitionally overlapping displayed-pivot adapter lemmas.

Durable review artifact:
`review-case2-selected-entry-chart-family-data-a4.md`.
