# A4 Case 2 Corrected Exponent Post-Data

Status: reproduced the corrected exponent post-data package and the supplied
post-state gap bridge.

## Source Data

Aoyagi's Case 2 discussion on PDF pp. 19-22 assigns new data at the label
`(S,J+1)`. The expedition has already separated the source mismatch:

- the PDF's printed vector before stage `S` uses actual widths;
- the printed scalar exponent uses the prefix minimum `M(S)`;
- substituting the printed vector into the terminal exponent formula gives
  `(M^(S)-J)(M^(S+1)-J)`, not `(M(S)-J)(M^(S+1)-J)` in general.

The current checkpoint therefore packages only the corrected prefix-minimum
certificate data. It is not a package of the PDF's printed vector.

## Reproduction

Let an old exponent certificate package at `(S,J)` assign:

```text
t_(s,k), numerator_(s,k), leastValue_(s,k)
```

to every introduced label. A supplied corrected Case 2 exponent post-state at
`(S,J+1)` consists of six equalities:

```text
t'_(s,k) = t_(s,k)                         for old introduced labels,
numerator'_(s,k) = numerator_(s,k)         for old introduced labels,
leastValue'_(s,k) = leastValue_(s,k)       for old introduced labels,

t'_(S,J+1) = correctedCase2PivotVector n S J,
numerator'_(S,J+1) = (mu_S-J)(n_(S+1)-J),
leastValue'_(S,J+1) = J.
```

The domain advance from `(S,J)` to `(S,J+1)` adds only the possible new label
`(S,J+1)`. Therefore:

- old labels are certified by rewriting through the three old-data equalities;
- the new label is certified by the existing corrected new-label certificate.

This proves the all-label exponent certificate package at `(S,J+1)`.

For the recurrence/gap bridge, suppose a supplied recurrence post-state also
preserves old levels and assigns the new label level `J`. If the old
least-value/level bridge holds, then the successor bridge follows label by
label:

- for old labels, use old least-value preservation and old level preservation;
- for `(S,J+1)`, use `leastValue'_(S,J+1)=J` and `level'_(S,J+1)=J`.

The old integer least-value gap also advances:

- old labels reduce to the old gap by least-value preservation;
- the new label has least value `J`, so it cannot satisfy
  `J+2 <= leastValue' < mu_S`.

Combining the successor bridge with the successor integer gap gives the
successor Nat-valued recurrence `case2Gap`.

## Scope

This is corrected certificate and invariant bookkeeping. It does not prove:

- that a blow-up chart produces the supplied recurrence or exponent post-data;
- that old exponent assignments are geometrically unchanged;
- source comparability;
- arbitrary-pivot transport;
- chart coverage, regularity, Jacobian facts, normal crossings, or RLCT
  extraction;
- that the corrected vector is the PDF's printed Case 2 vector.
