# A4 Case 1(2) J-Increment Payload

Status: reproduced the finite payload behind Aoyagi's statement that in the
displayed Case 1(2) continuation branch, `J` is increased by one.

## Source Situation

On PDF pp. 15-18, Case 1 starts from a first jump:

```text
b_(J+1) = ... = b_(J+J1),    b_(J+J1+1) != b_(J+J1),
```

equivalently there is no old label with `tilde t` value in
`J+1, ..., J+J1-1`. A selected old variable satisfies
`tilde t_(s,k)=J+J1`.

In Case 1(2), the displayed row-strip chart introduces the new selected
variable `u_(S,J+1)` and factors the old variable as

```text
u_(s,k) = u_(S,J+1) * u'_(s,k).
```

The printed new label has tail value `J` from layer `S` onward and its
numerator increment is

```text
J1 * (M^(S+1) - J).
```

This is actual-width arithmetic. It is not a prefix-minimum width.

After the displayed `Q` and `P` operations, PDF p. 18 says that if

```text
J+1 <= M(S+1) = min{M(S), M^(S+1)},
```

then the inductive statement holds with `J` increased by one.

## Pen-And-Paper Calculation

The finite-domain consequence of the continuation branch is local:

```text
(S,J)  -->  (S,J+1).
```

The fresh label is source-valid because the actual-width side condition gives

```text
J+1 <= M^(S+1).
```

The next-state index is source-bounded because the non-strict continuation
guard gives

```text
J+1 <= M(S+1).
```

This is the guard for landing at `(S,J+1)`. It is not a proof that the
post-increment residual block is nonempty; that would require the stricter
bound `J+2 <= M(S+1)`.

For the introduced-label finite domain, the old labels at `(S,J)` remain old,
and the only new current-layer label is `(S,J+1)`. Therefore

```text
introduced(S,J+1)
  = introduced(S,J) union {(S,J+1)}
```

as a disjoint finite insertion, so the cardinality increases by one.

The recurrence-weight update is relative to the factored-old base state. The
factored base contains the residual old variable `u'_(s,k)`. The supplied
post-state inserts the new label `(S,J+1)` at level `J` with variable
`u_(S,J+1)`, hence for every row level `i >= J+1`,

```text
post.weight_i = u_(S,J+1) * factoredBase.weight_i.
```

This must not be rewritten as a direct comparison with the substituted source
state, because that source state already contains the selected old factor at
level `J+J1`.

The exponent-domain payload is the existing supplied Case 1(2) new-label
certificate: the post exponent certificates live on `(S,J+1)`. Its proof still
uses the selected old certificate, `leastValue=level`, the flat-tail invariant,
and the source bounds packaged in the local handoff.

## Lean Boundary

Lean now names the payload:

```text
Case1DisplayedRowStripJIncrementPayload
```

and exposes it from the supplied Case 1(2) boundaries by

```text
Case1DisplayedRowStripSuppliedTransitionBoundary.jIncrementPayload
Case1DisplayedRowStripSelectedOldPullbackBoundary.jIncrementPayload
Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.jIncrementPayload
```

The recurrence projection is available as

```text
Case1DisplayedRowStripSuppliedTransitionBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge
Case1DisplayedRowStripSelectedOldPullbackBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge
Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge
```

## Caveats

- This is a finite payload over supplied Case 1(2) boundary data.
- It does not construct the chart or the post-state.
- It does not prove a nonempty residual block after the increment.
- It does not prove chart coverage, regularity, transition regularity, or a
  Jacobian formula.
- It does not prove the full Case 1 transition invariant.
- It does not prove a Lemma 5 classifier, injection, nonduplication theorem,
  back-to-label map, pole order, normal crossings, or RLCT extraction.
