# A4 Case 2 Exponent Update Data

Status: reproduced the concrete update-data wrapper for corrected Case 2
exponent-domain extension.

## Source Data

The finite exponent-domain package records, for each introduced label, a
vector `t`, a numerator exponent, and a least value. The corrected Case 2
new-label certificate already proves the one-label data for `(S,J+1)` using
the prefix-minimum repaired vector:

```text
t_(S,J+1) = correctedCase2PivotVector n S J,
numerator_(S,J+1) = (mu_S - J) * (n_(S+1) - J),
leastValue_(S,J+1) = J.
```

This is corrected certificate data, not the PDF's printed Case 2 vector.

## Reproduction

Assume an old certificate package over the introduced labels at `(S,J)`.
Define new total assignments by overriding only the new label `(S,J+1)`:

```text
t' = updateSelectedLabelVector(S,J+1, correctedCase2PivotVector, t),
numerator' = updateSelectedLabelScalar(S,J+1,
  (mu_S-J)(n_(S+1)-J), numerator),
leastValue' = updateSelectedLabelScalar(S,J+1, J, leastValue).
```

For every old introduced label, `(s,k) != (S,J+1)` because `(S,J+1)` is not
introduced before the `J`-advance. Therefore the update functions reduce to
the old assignments on old labels. At the new label, the update functions
reduce to the corrected Case 2 assignments.

The existing domain-extension theorem then extends the certificate package
from `(S,J)` to `(S,J+1)` under the continuation bound
`J+1 <= mu_(S+1)`.

## Scope

This is syntactic exponent-domain bookkeeping. It does not use
`Case2SuppliedPostData`, because recurrence `level/var` post-data does not
imply old exponent vectors, numerators, or least values are unchanged.

It does not prove chart production, exponent transition invariance, source
comparability, arbitrary-pivot transport, normal crossings, RLCT extraction,
or that the corrected vector is the PDF's printed vector.
