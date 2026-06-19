# A4 Case 2 Recurrence-Weight Update

Status: reproduced the narrow recurrence update behind Aoyagi's displayed
Case 2 line `b'_i = u_(S,J+1) b_i`.

## Source Data

Aoyagi's inductive recurrence on PDF pp. 14-15 is

```text
b_0 = 1,
b_i = (product over active labels with tilde_t_(s,k)=i-1 of u_(s,k)) * b_(i-1).
```

In Case 2, PDF pp. 19-21 advances from `(S,J)` to `(S,J+1)` in the displayed
pivot chart by introducing the new variable `u_(S,J+1)`. The active label set
changes by exactly the new actual-width source label `(S,J+1)`, and the source
assigns this new label level `tilde_t_(S,J+1)=J`.

This note uses the consistent normalization

```text
newWeight_i = u_(S,J+1) * oldWeight_i
```

and does not also count the standalone outside `u` in the later product display.

## Reproduction

Write

```text
m_r = product over active labels with level r of their variables,
b_(r+1) = m_r * b_r.
```

After the Case 2 `J`-advance, old labels keep their levels and variables, while
the new label has level `J` and variable `u`. Therefore

```text
m'_J = u * m_J,
m'_r = m_r    for r != J.
```

The recurrence gives equality before the new factor appears:

```text
b'_i = b_i,    i <= J.
```

At the next row,

```text
b'_(J+1) = m'_J * b'_J
         = (u*m_J) * b_J
         = u * b_(J+1).
```

For every later row, since `m'_r=m_r` for `r>J`,

```text
b'_(r+1) = m'_r * b'_r
         = m_r * (u*b_r)
         = u * b_(r+1).
```

Thus for all `i >= J+1`,

```text
b'_i = u * b_i.
```

If the old Case 2 gap also gives `b_(J+1)=...=b_(mu_S)`, then multiplying the
whole displayed residual strip by the same `u` preserves flatness:

```text
b'_(J+1)=...=b'_(mu_S).
```

## Scope

This is recurrence bookkeeping only. It assumes:

- the post-state keeps old introduced-label recurrence data unchanged,
- the new label `(S,J+1)` is source-valid,
- the new label has level `J`,
- the new label variable is the selected chart variable `u`.

It does not prove that the blow-up chart produces the post-state, does not
resolve the printed Case 2 vector mismatch, does not prove the source
comparability sentence, and does not address chart coverage, regularity,
exponent updates, termination, normal crossings, or RLCT extraction.
