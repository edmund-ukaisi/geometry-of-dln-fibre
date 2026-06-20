# A4 Case 2 Displayed Pivot-Complement Exhaustion

Status: reproduced the finite index translation from Aoyagi's displayed
post-pivot lower-right domain to Lean's pivot-complement row and column
types.  This is not the terminal matrix-shape theorem.

## Source Anchor

On PDF pp. 20-22, Aoyagi performs the displayed Case 2 pivot at the
top-left residual-block entry `(J+1,J+1)`, applies the displayed `Q` and `P`
operations, and then splits according to whether the next continuation
condition holds.  The terminal paragraph states that if the next bound fails,
then `D'''_J` is `(1,0,...,0)` or its transpose.

Lean's current checkpoint isolates only the finite index part behind that
sentence.  Before deleting the displayed pivot, the residual row and column
domains are

```text
rows    J+1, ..., M(S),
columns J+1, ..., M^(S+1).
```

After deleting the displayed pivot row and column, the lower-right complement
domains are

```text
rows    J+2, ..., M(S),
columns J+2, ..., M^(S+1).
```

## Pen-And-Paper Reproduction

Let

```text
mu_S    = M(S),
n_next  = M^(S+1),
mu_next = M(S+1) = min(mu_S, n_next).
```

The old residual row type is the finite subtype

```text
R_old = { i | J+1 <= i <= mu_S },
```

and the displayed pivot row is the element with raw value `J+1`.  Deleting
that pivot row gives

```text
{ i in R_old | i != J+1 }.
```

Because membership in `R_old` says `J+1 <= i <= mu_S`, the added condition
`i != J+1` is equivalent, over natural numbers, to `J+2 <= i`.  Hence

```text
{ i in R_old | i != J+1 }  ~=  { i | J+2 <= i <= mu_S }.
```

The same argument for the old residual column type

```text
C_old = { j | J+1 <= j <= n_next }
```

identifies

```text
{ j in C_old | j != J+1 }  ~=  { j | J+2 <= j <= n_next }.
```

The preceding post-pivot exhaustion checkpoint proved that if the next
continuation bound fails,

```text
not (J+2 <= mu_next),
```

then at least one of the two post-pivot finite intervals is empty.  Through
the displayed pivot-complement equivalences, this means at least one of the
two pivot-complement index types is empty.

Consequently any matrix indexed by the two displayed pivot-complement types
has no meaningful lower-right entries: if the row complement is empty, there
are no rows; if the column complement is empty, each row has no columns.  Thus
the lower-right matrix type is subsingleton, and over a type with zero every
such lower-right matrix is equal to the zero matrix.

## Boundaries

- This proves only the finite index/complement and lower-right domain-vacuity
  content.
- It is not Aoyagi's full terminal block theorem
  `D'''_J = (1,0,...,0)` or `D'''_J = (1,0,...,0)^t`.
- It does not construct `D'''_J`, prove the post-`Q/P` zero pattern for the
  whole block, choose a source chart branch, construct `C'^(S+1)`, or build
  the `S+1` recurrence/exponent state.
- It does not prove chart coverage, coordinate regularity, Jacobian/volume
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, or repair of the printed Case 2 vector mismatch.
