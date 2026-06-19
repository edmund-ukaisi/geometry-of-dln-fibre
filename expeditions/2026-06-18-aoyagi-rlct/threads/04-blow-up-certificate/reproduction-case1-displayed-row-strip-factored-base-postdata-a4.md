# A4 Case 1(2) Factored-Base Recurrence Post-Data

Status: reproduced the recurrence bookkeeping boundary for the displayed
Case 1(2) row-strip branch.

## Source Facts

On printed p. 17, Case 1(2), Aoyagi factors the selected old variable as

```text
u_(s,k) = u_(S,J+1) u'_(s,k).
```

The PDF then displays the fresh label `(S,J+1)` and the row-weight relation

```text
b'_(J+1) = u_(S,J+1) b_(J+1), ..., b'_(M(S)) = u_(S,J+1) b_(M(S)).
```

It does not print a complete post-recurrence assignment for every old label.
In particular, the residual old variable `u'_(s,k)` remains by chart
coordinates, but the PDF does not separately display post values
`t'_(s,k)`, `tilde_t'_(s,k)`, or `M'_(s,k)`.

## Pen-And-Paper Model

Let `h = J + J1`, where `1 <= J1`.  The monomial recurrence convention is

```text
b_0 = 1,
b_(r+1) = step_r * b_r.
```

Thus a label at level `r` first affects row weight `b_(r+1)`.

Use three recurrence viewpoints:

```text
baseStep:
  old selected variable already replaced by the residual old variable old'
  at level h;

sourceStep:
  original source substitution old = u * old' at level h;

postStep:
  baseStep plus the fresh label (S,J+1) with variable u at level J.
```

Then:

```text
sourceWeight_i = baseWeight_i,       i <= h,
sourceWeight_i = u * baseWeight_i,   h+1 <= i,

postWeight_i = baseWeight_i,         i <= J,
postWeight_i = u * baseWeight_i,     J+1 <= i.
```

So the post recurrence satisfies Aoyagi's displayed formula

```text
postWeight_i = u * baseWeight_i
```

on the whole residual row range `J+1 <= i`.

The original source-substituted weights differ from the post weights only on
the strip rows `J+1 <= i <= h`: on those rows the `u` is supplied by the
divided matrix entries, while below the strip it is already present in the old
source row weights. This is exactly the convention encoded by
`case1RowStripOldWeight`.

## Lean Boundary

Lean names the recurrence boundary

```text
Case1DisplayedRowStripFactoredBasePostData
```

as a thin alias for the existing successor post-data package, but applied to a
`factoredBase` state, not the original pre-chart state.

The new source-order theorem is

```text
IntroducedLabelRecurrenceState.Case2SuppliedPostData
  .exists_case1DisplayedRowStrip_sourceOrder_identity_succWeights_of_postData
```

It starts from the factored-base row-strip source block

```text
diagonal (case1RowStripOldWeight strip u factoredBaseWeight)
  * case1RowStripSourceMatrix strip u A
```

and rewrites the resulting post-pivot row weights as `post.weight` using the
supplied post-data update.

## Caveats

- This is not a chart-production theorem.
- It does not relate the original pre-state to the factored-base state.
- It does not prove hidden old-label source validity.
- It does not prove complete old-label post assignments.
- It does not prove chart coverage, regularity, Jacobian accounting, normal
  crossings, or RLCT extraction.
