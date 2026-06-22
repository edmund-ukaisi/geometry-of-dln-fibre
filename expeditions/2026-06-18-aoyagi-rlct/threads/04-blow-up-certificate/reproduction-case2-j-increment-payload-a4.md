# A4 Case 2 Displayed J-Increment Payload

Status: reproduced the finite payload behind Aoyagi's displayed Case 2
statement that the continuation branch has `J` increased by one.

## Source Situation

On PDF pp. 19-21, Case 2 assumes

```text
b_(J+1) = ... = b_M(S),
```

equivalently there is no old label with `tilde t` value in
`J+1, ..., M(S)-1`.

The displayed top-left chart introduces the selected variable `u_(S,J+1)`.
The printed recurrence assignment is

```text
b'_(J+1) = u_(S,J+1) b_(J+1),
...
b'_M(S) = u_(S,J+1) b_M(S).
```

After the displayed `Q` and `P` operations, PDF p. 21 says that if

```text
J+1 <= M(S+1) = min{M(S), M^(S+1)},
```

then the inductive statement holds with `J` increased by one.

## Corrected Exponent Boundary

The source also prints the Case 2 new vector with actual previous widths in
the entries before layer `S`, while the printed numerator is

```text
(M(S) - J) * (M^(S+1) - J).
```

Earlier A4 checks record the mismatch: substituting the printed vector into
the terminal-exponent formula gives

```text
(M^(S) - J) * (M^(S+1) - J),
```

unless `M(S)=M^(S)`. Therefore this slice uses the existing corrected Case 2
exponent package in Lean. The correction is a Lean certificate boundary, not a
claim that the printed vector already has the corrected numerator.

## Pen-And-Paper Calculation

The finite-domain consequence of the continuation branch is again local:

```text
(S,J)  -->  (S,J+1).
```

The non-strict source guard gives the next-state bound

```text
J+1 <= M(S+1).
```

This supports landing at `(S,J+1)`. It is not a proof that the post-increment
residual block is nonempty; that would require `J+2 <= M(S+1)`.

Actual-width validity of the fresh label follows from the same guard, because

```text
M(S+1) <= M^(S+1).
```

For the introduced-label finite domain, the old labels at `(S,J)` remain old,
and the only new current-layer label is `(S,J+1)`. Hence

```text
introduced(S,J+1)
  = introduced(S,J) union {(S,J+1)}
```

as a disjoint finite insertion, and the cardinality increases by one.

The supplied recurrence post-data records the displayed weight update:

```text
post.weight_i = u_(S,J+1) * pre.weight_i
```

for every row level `i >= J+1`.

The corrected exponent post-data records:

```text
numerator'_(S,J+1)
  = correctedCase2NewLabelNumerator n S J
  = |case2ResidualBlockPivotEntries n S J|.
```

and extends the exponent certificate domain to `(S,J+1)`.

## Lean Boundary

Lean now names the payload:

```text
Case2DisplayedJIncrementPayload
```

and exposes it through the displayed Case 2 supplied boundary:

```text
Case2DisplayedSuppliedChartFamilyBoundary.jIncrementPayload
```

The recurrence projection is available as

```text
Case2DisplayedSuppliedChartFamilyBoundary.post_weight_eq_new_mul_pre_weight_of_ge
```

## Caveats

- This is a finite payload over supplied displayed Case 2 boundary data.
- It uses the corrected Case 2 exponent package already isolated in Lean.
- It does not repair the printed Case 2 vector mismatch as a source theorem.
- It does not construct the chart or the post-state.
- It does not prove a nonempty residual block after the increment.
- It does not prove successor chart-family construction, full next
  `C'^(S+1)`, transition invariance, Jacobian arithmetic, normal crossings,
  pole order, or RLCT extraction.
