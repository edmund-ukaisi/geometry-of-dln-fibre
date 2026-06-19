# A4 Case 1(2) Displayed Row-Strip Quotients

Status: reproduced the quotient witnesses used by Aoyagi's displayed
Case 1(2) `P` matrix.

## Source Facts

Aoyagi defines row weights by the recurrence

```text
b_0 = 1,
b_i = (product over labels with tilde_t = i-1) * b_(i-1).
```

In Case 1, the first-jump condition is

```text
b_(J+1) = ... = b_(J+J1),
b_(J+J1+1) != b_(J+J1),
```

equivalently no active label has `tilde_t` in
`J+1, ..., J+J1-1`.  Aoyagi chooses an old label with
`tilde_t = J+J1`.

In Case 1(2), the displayed pivot chart factors

```text
u_(s,k) = u_(S,J+1) u'_(s,k)
```

and Aoyagi's `P` matrix has first-column entries

```text
-(b'_i / b'_(J+1)) d''_(i,J+1),
```

for rows `i = J+2, ..., M(S)`.  The paper calls `P` regular, but the quotient
regularity is implicit.

## Pen-And-Paper Derivation

Let `step r` be the product of active variables whose level is `r`, after
replacing the selected old variable by `u'_(s,k)` rather than
`u_(S,J+1)u'_(s,k)`.  Let

```text
c_i = monomialRec step i.
```

The selected variable is counted once by setting post row weights

```text
B_i = u * c_i,    u = u_(S,J+1).
```

For strip rows `J+2 <= i <= J+J1`, the first-jump gap gives
`step r = 1` for `J+1 <= r < J+J1`, hence `c_i = c_(J+1)`.
The quotient witness is `q_i = 1`.

For lower residual rows `J+J1+1 <= i <= M(S)`, the ordinary recurrence gives
a right-oriented tail product

```text
c_i = q_i * c_(J+1).
```

Multiplying both sides by the common selected factor gives

```text
B_i = u * c_i = q_i * (u * c_(J+1)).
```

No cancellation of `u`, inverse, or division is needed.

## Lean Boundary

Lean proves this at the finite recurrence level:

```text
exists_case1DisplayedRowStripPivot_quotients_of_rowIndex_monomialRec
exists_case1DisplayedRowStripPivot_pivotMul_quotients_of_rowIndex_monomialRec
exists_case1DisplayedRowStripPivot_pivotMul_quotients_of_recurrenceState
```

It also provides source-order wrappers that choose quotient witnesses and feed
them into the existing row-strip source identity:

```text
exists_case1RowStrip_sourceOrder_identity_of_rowIndex_monomialRec
exists_case1DisplayedRowStrip_sourceOrder_identity_of_rowIndex_monomialRec
```

These wrappers use only row-level lower bounds for the displayed top-left
pivot row `J+1`.  They do not use the Case 1 first-jump gap as a full Case 2
gap.

## Caveats

- This is not a Case 1 transition theorem.
- The normalised chart matrix, strip predicate, hidden old-variable
  factorisation convention, and following factor remain supplied.
- The hidden old label is not encoded by the finite `Unit` branch.
- No chart construction, chart coverage, regularity, Jacobian formula,
  exponent post-data, normal crossings, or RLCT extraction is proved.
