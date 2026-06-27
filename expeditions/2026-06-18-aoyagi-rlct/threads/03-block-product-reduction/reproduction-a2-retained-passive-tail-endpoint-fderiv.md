# Reproduction - A2 Retained-Passive Tail Endpoint Frechet Derivative

Date: 2026-06-27.

Status: controller pen-and-paper reproduction before Lean formalisation.

## Setup

For retained-passive top-left seed factors write

```text
A_i(y) = (ofTopologyTuple y).A1seed_i,
j = Fin.last (M+1),
P_i(y) = residualFactorProduct A(y) j i.
```

The actual retained-passive tail after the first edge is

```text
Tail_M(y) = retainedPassiveA1TailAfterFirst A(y) = P_1(y).
```

It is the ordered product

```text
A_M(y) * ... * A_1(y),
```

with the empty product convention when `M=0`.  The dummy seed `A_0` is not a
factor of `Tail_M`.

## Empty Tail

When `M=0`, the start index `1` is already the terminal index `j`.  Therefore

```text
Tail_0(y) = P_j(y) = 1,
```

and hence

```text
d(Tail_0)_z(v) = 0.
```

This is a constant-map derivative calculation; it uses no determinant-chart
hypothesis.

## First Passive Step

For a nonempty passive tail, write the number of passive factors as `M+1`.
Let

```text
q = 0 : Fin (M+1),
p = q.succ.
```

Then `p` is the first passive seed index, so `p.castSucc` is the tail start
index `1`.  The recurrence already reproduced and proved for suffix products
gives

```text
d(P_{p.castSucc})_z(v)
  = d(P_{p.succ})_z(v) * A_p(z)
    + P_{p.succ}(z) * v.A1passive_0.
```

Since `P_{p.castSucc} = Tail_{M+1}`, this specializes to

```text
d(Tail_{M+1})_z(v)
  = d(P_2)_z(v) * A_1(z)
    + P_2(z) * v.A1passive_0.
```

Equivalently, for an arbitrary `M` with `hM : 0 < M`, take
`q = ⟨0,hM⟩ : Fin M` and the same formula gives the positive-length wrapper
for `Tail_M`.

Here `P_2` means the suffix after the first passive factor.  If there is only
one passive factor, then `P_2` is the empty suffix, so its derivative term is
zero by the endpoint theorem; this slice does not need to simplify that
subcase.

## Kill Conditions

- If `A_0` appears in `Tail_M`, the theorem is using the full product instead
  of the passive tail after the first edge.
- If the noncommutative order is changed to `A_p * d(P_{p.succ})` or
  `v.A1passive_0 * P_{p.succ}`, the formula is wrong.
- If the theorem requires determinant-chart membership or invertibility, it is
  overspecified: this endpoint derivative is just the product rule.
- If the theorem is described as a closed finite-sum formula for `dTail`, it
  overclaims.

## Nonclaims

This does not prove a closed finite-sum formula for `dTail`, full `Ctop`
source staging, `F3` source staging, determinant equality, measure transport,
normal crossings, pole order, or RLCT.
