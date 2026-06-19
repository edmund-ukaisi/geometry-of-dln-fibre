# A4 Case 2 Successor Source Substitution

Status: reproduced the displayed Case 2 source-substitution bridge from old
row weights to supplied successor recurrence weights.

## Source Data

Aoyagi's recurrence on PDF pp. 14-15 defines row weights by

```text
b_0 = 1,
b_i = m_(i-1) b_(i-1),
```

where `m_r` is the product of variables whose current level is `r`.

In the displayed Case 2 chart on PDF pp. 19-21, the selected entry is
`u = u_(S,J+1)` and the residual block is substituted as

```text
D_J = u D'_J.
```

The source also prints the recurrence update

```text
b'_i = u b_i
```

for the displayed residual row range. The consistent normalization is to count
the selected variable once, inside the supplied successor weights `b'_i`.

## Reproduction

Let `pre` be the recurrence state at `(S,J)` and let `post` be supplied at
`(S,J+1)`. Assume old introduced labels keep the same levels and variables,
and that the new label `(S,J+1)` has level `J` and variable `u`.

The recurrence-weight calculation from the previous checkpoint gives

```text
post.weight_i = u * pre.weight_i,    i >= J+1.
```

For the displayed residual row indexed by a source row level `r` with
`J+1 <= r <= mu_S`, this is

```text
b'_r = u b_r.
```

The source-substituted residual block is

```text
D_J = u D'_J.
```

Therefore row weighting gives

```text
diag(b) D_J
  = diag(b) (u D'_J)
  = diag(u b) D'_J
  = diag(b') D'_J.
```

After putting the displayed pivot first, the pivot row has weight
`post.weight_(J+1)` and each lower residual row indexed by `r` has weight
`post.weight_r`.

If the old Case 2 gap makes the old displayed residual row weights flat, then
the existing displayed `Q/P` identity applies to the same source-substituted
left side, while the cleared right-side diagonal can be written with these
post weights.

## Scope

This is still local finite algebra plus conditional recurrence bookkeeping.
It assumes:

- the post-state keeps old introduced-label recurrence data unchanged;
- the new label `(S,J+1)` has level `J`;
- the new label variable is the selected chart variable `u`;
- the old state satisfies the Case 2 gap when the `Q/P` wrapper is used.

It does not prove that the blow-up chart produces the post-state, does not
prove chart coverage or regularity/Jacobian facts, does not repair the printed
Case 2 vector mismatch, does not prove source comparability, and does not
double-count the standalone outside `u` in the PDF display.
