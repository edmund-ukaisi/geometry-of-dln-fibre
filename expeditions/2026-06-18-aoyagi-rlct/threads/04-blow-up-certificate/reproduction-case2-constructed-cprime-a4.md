# Pen-and-paper reproduction - Case 2 constructed `Cprime`

Status: checked finite matrix algebra.

This note records the reverse coordinate direction for Aoyagi's displayed Case
2 column operation.  It stays in pivot-first coordinates and does not construct
a total source-coordinate following function.

## Source

Aoyagi PDF pp. 19-22 displays the Case 2 column operation

```text
C' = Q^-1 C.
```

The forward Lean API already names this as

```text
case2DisplayedPaperCprime = Q^-1 * Csrc,
```

where `Csrc` is the source following factor after restriction and pivot-first
column reindexing.

## Reverse Coordinate Direction

If `Cprime` is taken as the chart coordinate, the corresponding old
pivot-first following factor is

```text
Csrc := Q * Cprime.
```

Then the inverse operation recovers the chart coordinate:

```text
Q^-1 * (Q * Cprime) = (Q^-1 * Q) * Cprime = Cprime.
```

The displayed post-`Q` block is

```text
D'' = D_chart * Q.
```

Therefore

```text
D'' * Cprime = (D_chart * Q) * Cprime
             = D_chart * (Q * Cprime).
```

This is the finite coordinate direction needed before any stronger chart
production theorem: it makes `Cprime` a free pivot-first matrix coordinate and
reconstructs the old pivot-first following factor algebraically.

## Lean Targets

```text
case2DisplayedPaperConstructedFollowingFactor
case2DisplayedPaperCprime_of_constructedFollowingFactor
case2DisplayedPaperDpp_mul_constructedCprime
```

## Nonclaims

- No total source-coordinate function `ℕ -> τ -> R` is constructed from
  `Cprime`.
- No chart coverage, chart regularity, Jacobian arithmetic, recurrence
  post-data, exponent post-data, transition invariant, normal crossing, RLCT
  extraction, arbitrary-pivot coverage, terminal relabeling, or printed-vector
  repair is proved.
