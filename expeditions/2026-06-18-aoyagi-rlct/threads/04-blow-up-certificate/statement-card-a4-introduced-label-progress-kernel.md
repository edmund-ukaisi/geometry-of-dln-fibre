# Statement card - A4 introduced-label progress kernel

Date: 2026-06-29.

## Statement

Strict growth of the finite introduced-label support gives a well-founded
progress relation for Aoyagi blow-up branch states.  The displayed Case 2
same-stage pivot advance `(S,J) -> (S,J+1)` is one such progress step whenever
`J+1` is within the actual source width, and hence also under the Case 2
prefix-minimum continuation bound.

Lean targets:

```text
AoyagiIntroducedLabelBranchState
AoyagiIntroducedLabelBranchState.progressStep_wellFounded
AoyagiIntroducedLabelBranchState.support_ssubset_case2_increment
AoyagiIntroducedLabelBranchState.progressStep_case2_increment
AoyagiIntroducedLabelBranchState.progressStep_case2_increment_of_prefixBound
```

## Source Reference

Aoyagi PDF pp. 19-22 for the displayed Case 2 continuation branch, where the
same-stage index `J` is advanced by one.  The finite support/remaining-label
well-foundedness proof is expedition bookkeeping.

## Dependencies

- `actualWidthLabelFinset`
- `introducedLabelFinset`
- `introducedLabelFinset_subset_of_state_le`
- `not_introducedLabel_case2_new_before`
- `introducedLabel_case2_new_after`
- `prefixMinNat_le_width`

## Assumptions Kept Explicit

- finite layer bound `L`;
- natural width function `n`;
- branch state bounds `1 <= S` and `S <= L`;
- actual-width or prefix-minimum bound for the Case 2 increment.

## Nonclaims

This does not construct source-production payloads, prove branch guard
exhaustiveness, prove all Case 1/Case 2 transitions are progress steps, fill
`SelectedEntryBranchTerminationData`, construct a full analytic atlas producer,
extract normal crossings, compute pole order, or extract an RLCT.

## Reproduction and Review

Reproduction:

```text
threads/04-blow-up-certificate/reproduction-a4-introduced-label-progress-kernel.md
```

Review:

```text
threads/04-blow-up-certificate/review-a4-introduced-label-progress-kernel.md
```
