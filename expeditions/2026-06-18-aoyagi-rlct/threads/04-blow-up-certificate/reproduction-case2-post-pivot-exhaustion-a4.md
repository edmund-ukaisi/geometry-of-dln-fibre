# A4 Case 2 Post-Pivot Exhaustion Boundary

Status: reproduced the finite lower-right domain check after Aoyagi's
displayed Case 2 pivot.  This is not the `S+1` advance transition.

## Source Anchor

On PDF pp. 20-22 Aoyagi performs the displayed Case 2 pivot at the top-left
entry of the residual block.  In old `(S,J)` notation the center before the
pivot has row and column ranges

```text
rows    J+1, ..., M(S),
columns J+1, ..., M^(S+1).
```

After pivoting at `(J+1,J+1)`, the lower-right block available for another
`J`-advance has ranges

```text
rows    J+2, ..., M(S),
columns J+2, ..., M^(S+1).
```

Aoyagi's prose then distinguishes the case where the induction continues in
`J` from the case where the displayed block is exhausted and the construction
advances to `S+1`.  The paper reuses/relabels indices at this point; in Lean's
old `(S,J)` notation, the next continuation bound is

```text
J+2 <= M(S+1) = min(M(S), M^(S+1)).
```

## Pen-And-Paper Reproduction

Let

```text
mu_S    = M(S),
n_next  = M^(S+1),
mu_next = M(S+1) = min(mu_S, n_next).
```

The post-pivot lower-right row and column sets are

```text
R_post = { i | J+2 <= i <= mu_S },
C_post = { j | J+2 <= j <= n_next }.
```

Their cardinalities are the interval counts

```text
|R_post| = mu_S - (J+1),
|C_post| = n_next - (J+1),
```

and the post-pivot entry set has cardinality

```text
|R_post x C_post|
  = (mu_S - (J+1))(n_next - (J+1)).
```

The product set is nonempty exactly when both sides are nonempty:

```text
R_post x C_post nonempty
iff J+2 <= mu_S and J+2 <= n_next
iff J+2 <= min(mu_S, n_next)
iff J+2 <= mu_next.
```

Therefore failure of the next continuation bound,

```text
not (J+2 <= mu_next),
```

implies the lower-right entry set is empty.  More explicitly, since
`min(mu_S,n_next) <= J+1`, either `mu_S <= J+1` or `n_next <= J+1`; in the
first case the post-pivot row set is empty, and in the second case the
post-pivot column set is empty.

If the displayed pivot was valid,

```text
J+1 <= mu_next,
```

and the next pivot is not valid, then `mu_next = J+1`.  This is the precise
old-notation version of the boundary between continuing with `J` advanced and
leaving the displayed Case 2 block.

## Boundaries

- This proves only finite row/column/product-domain arithmetic.
- It does not construct `D'''_J`, the new `C'^(S+1)`, or any `S+1` recurrence
  state.
- It does not prove termination, chart coverage, coordinate regularity,
  Jacobian/volume arithmetic, normal crossings, RLCT extraction, exponent
  updates, or a transition invariant.
- Rectangular residual blocks are allowed; exhaustion may occur on the row
  side or the column side.
