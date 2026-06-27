# Reproduction - A2 Retained-Passive Tail Product FDeriv Recursion

Date: 2026-06-27.

Status: pen-and-paper reproduction for the recursive product-rule step for the
passive top-left tail derivative.  This is a recurrence for the derivative of
the ordered tail product, not a closed finite-sum formula.

## Setup

Let

```text
j = Fin.last (M+1),
A(y) = (ofTopologyTuple y).A1seed.
```

For an index `i <= j`, write

```text
P_i(y) = residualFactorProduct A(y) j i.
```

Thus `P_i` is the ordered product of passive top-left seed factors from the
right endpoint down to `i`.  The retained-passive tail after the first edge is

```text
Tail(y) = P_{1}(y).
```

It contains `A1seed 1, ..., A1seed M`, and it does not contain the dummy seed
`A1seed 0`.

## Endpoint

At the endpoint `i=j`, the residual product is the empty product:

```text
P_j(y) = 1.
```

Therefore

```text
d(P_j)_z(v) = 0.
```

This covers the `M=0` retained-passive tail case, because then
`Tail = P_j = 1`.

## Recursive Step

For `q : Fin M`, set

```text
p = q.succ : Fin (M+1).
```

The residual-product recursion gives

```text
P_{p.castSucc}(y) = P_{p.succ}(y) * A(y)_p.
```

Since `p=q.succ`, the seed factor is a passive top-left source coordinate:

```text
A(y)_p = (ofTopologyTuple y).A1passive q.
```

Therefore its Frechet derivative in direction `v` is

```text
d(A_p)_z(v) = v.A1passive_q.
```

Applying the product rule gives

```text
d(P_{p.castSucc})_z(v)
  = d(P_{p.succ})_z(v) * A(z)_p
    + P_{p.succ}(z) * v.A1passive_q.
```

This is the desired recursive formula.  The multiplication order is fixed:
the derivative of the already-built suffix product stays on the left of
`A(z)_p`, and the suffix product `P_{p.succ}(z)` left-multiplies the new
source tangent `v.A1passive_q`.

## Relation To `dTail`

For `0 < M`, `Tail = P_{(0 : Fin M).succ.castSucc}`, so the recurrence starts
with `q=0`.  For `M=0`, `Tail` is already the endpoint empty product and its
derivative is zero.

This slice stops at the recurrence.  Iterating the recurrence into a closed
finite sum is a separate theorem.

## Kill Conditions

- If the formula includes `A1seed 0` in `Tail`, the index orientation is wrong.
- If the product-rule terms are reversed, the formula is wrong because matrix
  multiplication is noncommutative.
- If `(fderiv A1seed_p) z v` is left opaque for `p=q.succ`, the theorem misses
  the source-tangent content of the passive tail recurrence.
- If the statement requires determinant-chart membership, it is overspecified:
  the product rule does not use invertibility.
- If this is described as a closed finite-sum formula for `dTail`, it
  overclaims.

## Nonclaims

No closed finite-sum formula, no inverse-tail derivative, no full `Ctop` source
staging, no `F3` source staging, no determinant-one shear, no determinant
equality, no measure theorem, no normal crossings, no pole order, and no RLCT
statement is proved by this slice.
