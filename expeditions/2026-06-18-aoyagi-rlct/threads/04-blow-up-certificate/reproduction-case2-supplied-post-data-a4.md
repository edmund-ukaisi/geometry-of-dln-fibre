# A4 Case 2 Supplied Post-Data Package

Status: reproduced the assumption package behind the conditional Case 2
recurrence update.

## Source Data

Aoyagi's recurrence on PDF pp. 14-15 determines row weights from introduced
exceptional variables and their current levels. In the displayed Case 2 chart
on PDF pp. 19-21, the `J`-advance introduces the new variable
`u_(S,J+1)` and assigns the new label `(S,J+1)` level `J`.

The elementary recurrence calculation only uses the following post-data:

```text
old labels keep their levels,
old labels keep their variables,
level(S,J+1) = J,
var(S,J+1) = u.
```

It does not use the displayed pivot bounds, the Case 2 gap, or the corrected
terminal-exponent certificate until later consequences.

## Reproduction

Let `pre` be the recurrence state at `(S,J)` and `post` a supplied recurrence
state at `(S,J+1)`. If old introduced labels agree and the new label has level
`J` and variable `u`, then the recurrence factors satisfy

```text
m'_J = u m_J,
m'_r = m_r    for r != J,
```

provided the new label is source-valid. Hence

```text
b'_i = u b_i,    i >= J+1.
```

If the old Case 2 gap is also supplied, then old displayed residual weights
are flat; multiplying every residual row weight by the same selected variable
keeps the successor residual weights flat.

If the corrected Case 2 new-label certificate is supplied, its introduced-label
field gives the source-validity of `(S,J+1)`, so the same recurrence update can
be used in the source-facing displayed `Q/P` wrappers.

## Scope

The package is recurrence-local. It does not include:

- the old Case 2 gap;
- displayed pivot bounds `1 <= S` and `J+1 <= mu_(S+1)`;
- the corrected new-label certificate;
- chart production, regularity, Jacobian, chart coverage, or exponent-update
  data.

This avoids turning a supplied post-state assumption into a transition theorem.
