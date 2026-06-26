# Reproduction - A2 Retained-Passive Solved Family Constructors

Date: 2026-06-26.

Status: pen-and-paper prerequisite for making the omitted endpoint formulas
construction data.  This is finite fixed-base algebra only.

## Question

The latest fixed-base readback package still assumes two endpoint equations:

```text
A1_0 = Tail^{-1} * Ctop,
A3_last = -(F3 - EarlyTail) * CtopLast.
```

The next constructor rung should define the full `A1` and `A3` families from
passive seed data so these equations are definitional consequences rather than
external hypotheses.

## Solving `A1_0`

Start with passive top-left seed data `A1seed_p` for every edge.  The value at
`p=0` is a placeholder; the passive tail ignores it:

```text
Tail = A1seed_last * ... * A1seed_1.
```

Given the active top-left endpoint `Ctop`, define the solved family by

```text
A1sol_0 = Tail^{-1} * Ctop,
A1sol_p = A1seed_p       for p != 0.
```

Then the endpoint equation consumed by the prior theorem is immediate:

```text
A1sol_0 = Tail(A1seed)^{-1} * Ctop.
```

Because `Tail` only sees the edges `p != 0`, the passive-tail unit hypothesis
on `A1seed_p` for `p != 0`, together with `det(Ctop)` unit, gives the full
determinant-unit family for `A1sol`.

## Solving `A3_last`

Start with passive lower-left seed data `A3seed_p` for every edge.  The final
value is a placeholder.  Given the solved `A1sol`, residual blocks `C_p`, and
active lower-left endpoint `F3`, compute the early signed tail by zeroing the
final lower-left block:

```text
A3early = A3seed with A3_last replaced by 0,
EarlyTail = Tail_0(A1sol,A3early,C).
```

Let

```text
CtopLast = residualFactorProduct(A1sol,last,lastEdge.castSucc).
```

Define the solved lower-left family by

```text
A3sol_last = -(F3 - EarlyTail) * CtopLast,
A3sol_p    = A3seed_p              for p != last.
```

Then `A3sol` satisfies exactly the endpoint equation consumed by the prior
package theorem:

```text
A3sol_last = -(F3 - EarlyTail(A3sol without last)) * CtopLast.
```

The only point to check is that the early tail is unchanged when replacing the
final placeholder by the solved final value, because `A3early` zeroes the
final block before forming the tail.

## Nonclaims

This does not define the full coordinate domain and does not prove a two-sided
local inverse.  It does not prove source-rank coverage, source/image equality,
source-measure pushforward, density/Jacobian accounting, normal crossings,
pole order, or RLCT extraction.
