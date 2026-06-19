# A4 Pivot-First Diagonal Weight Transport

Status: checked finite matrix reindexing reproduction.

## Scope

The pivot-first `Q/P` theorem uses the split diagonal matrix

```text
diag(b0, b_i)
```

where `b0` is the pivot-row weight and `b_i` are the non-pivot row weights in
pivot-first order. This note isolates the elementary transport from an
original row-weight function to that split diagonal matrix.

This is finite matrix algebra only. It does not prove Aoyagi's recurrence
flatness hypotheses, selected-entry charts, chart coverage, or exponent
updates.

## Reproduction

Let `weight : I -> R` be row weights and choose a pivot row `i0 : I`.
The original diagonal matrix is:

```text
diagonal weight : Matrix I I R.
```

Reindexing both rows and columns by the pivot-first equivalence gives:

```text
(diagonal weight).submatrix
  (pivotFirstIndexEquiv i0) (pivotFirstIndexEquiv i0).
```

The pivot-first split diagonal is:

```text
weightedPivotDiagonal (weight i0)
  (fun i : {i // i != i0} => weight i).
```

These matrices are equal. The off-diagonal blocks are zero by the diagonal
matrix definition, and the lower-right block is the diagonal of the non-pivot
row weights.

## Lean Shape

Lean proves:

```text
weightedPivotDiagonal_eq_pivotFirst_diagonal
```

This identifies the split diagonal used in `P` with the original row-weight
diagonal after pivot-first row reindexing.

## Kill Conditions

- The theorem only transports a supplied row-weight function. It does not prove
  that Aoyagi's `b_i` recurrence has been assigned correctly.
- It does not prove flatness, divisibility, or quotient witnesses; those are
  separate theorems already recorded.
- It does not prove source coordinate construction, regularity, chart
  coverage, exponent update, or transition invariants.
