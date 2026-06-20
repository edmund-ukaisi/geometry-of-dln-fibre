# A4 Case 2 Corrected Post-Data Center Count

Status: reproduced the supplied corrected post-data projection to the displayed
residual-block coordinate count.

## Source Situation

The displayed Case 2 residual block has rows

```text
J+1 <= i <= M(S)
```

and actual-width columns

```text
J+1 <= j <= M^(S+1).
```

The previous center-count checkpoint proved that the number of selected
residual-block coordinates is

```text
(M(S)-J)(M^(S+1)-J).
```

The supplied corrected Case 2 exponent post-data assigns the new label
`(S,J+1)` the numerator

```text
M'_(S,J+1) = (M(S)-J)(M^(S+1)-J).
```

## Reproduction

Let `N` be the selected residual-block coordinate count. From the row and
column intervals,

```text
N = |{J+1,...,M(S)}| * |{J+1,...,M^(S+1)}|
  = (M(S)-J)(M^(S+1)-J).
```

The corrected exponent post-data field for the new label states

```text
numerator'_(S,J+1) = (M(S)-J)(M^(S+1)-J).
```

Therefore, under the displayed continuation bound

```text
J+1 <= M(S+1),
```

which supplies the row and column integer-subtraction bounds, we get

```text
numerator'_(S,J+1) = N.
```

This is a projection from supplied corrected post-data to the already-proved
finite count. It does not derive the post-data from the chart.

## Scope / Caveats

- This is supplied exponent-bookkeeping only.
- The count uses prefix-minimum rows and actual-width columns.
- The equality to an integer cardinality uses continuation to avoid truncated
  subtraction issues.
- This is not a chart-production theorem.
- This is not a Jacobian exponent or volume-form calculation.
- This does not prove chart coverage, coordinate regularity, normal crossings,
  RLCT extraction, termination, or a transition invariant.
- This does not repair the printed Case 2 vector mismatch; it uses the
  corrected prefix-minimum post-data package.
