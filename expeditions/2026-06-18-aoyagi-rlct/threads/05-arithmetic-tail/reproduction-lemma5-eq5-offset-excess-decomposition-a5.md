# Pen-and-paper reproduction - Lemma 5 equation (5) offset/excess decomposition

Status: checked finite count decomposition.

This note records a pure arithmetic bridge between the already-formalised
same-coordinate interval excess and the equation `(5)` offset-value count.  It
does not construct Aoyagi's displayed vectors.

## Source

Aoyagi Lemma 5 counts intervals

```text
I_p = { H : Htilde_p <= H <= Htilde'_p }
```

through their excess

```text
e_p = |I_p|-1 = Htilde'_p - Htilde_p.
```

Equation `(5)` uses the offset

```text
alpha = Htilde'_p + 1 - k
```

with the source guard `alpha < p`.  The already-formalised Eq5 offset-value
set therefore counts offsets

```text
1 <= alpha <= min(e_p, p-1).
```

Its cardinality is

```text
min(e_p, p-1).
```

## Arithmetic

The interval excess is

```text
e_p = min(p, ell-p, a, ell-a).
```

There are two cases.

If

```text
1 <= p,  p <= a,  p <= ell-a,
```

then, assuming `a <= ell`, also `p <= ell-p`.  Hence

```text
e_p = p.
```

The Eq5 strict-offset count is then

```text
min(e_p, p-1) = p-1,
```

so one additional value remains:

```text
e_p = min(e_p,p-1) + 1.
```

If the rising inequalities fail, then either `p=0`, or `a<p`, or
`ell-a<p`.  In each case

```text
e_p <= p-1,
```

so

```text
min(e_p,p-1)=e_p,
```

and no extra rising contribution remains.

Thus pointwise:

```text
e_p = min(e_p,p-1) + indicator(1<=p and p<=a and p<=ell-a).
```

After rewriting `min(e_p,p-1)` as the cardinality of the Eq5 offset-value set,
this is the Lean theorem.

## Lower Endpoint

In the rising case, the missing value is the lower endpoint.  Indeed, under
`p <= a` and `p <= ell-a`, the gap formula gives

```text
Htilde'_p - Htilde_p = p.
```

If the lower endpoint were an Eq5 strict-offset value, then for some

```text
1 <= alpha <= min(e_p,p-1) = p-1
```

we would have

```text
Htilde_p = Htilde'_p - alpha.
```

Subtracting from the gap gives `alpha=p`, contradicting `alpha<=p-1`.
Thus the strict Eq5 offset set does not contain the lower endpoint when the
excess is controlled by the coordinate `p`.

## Lean Target

```text
aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator
aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min
```

## Nonclaims

- No construction or existence proof for equation `(5)`'s displayed vector.
- No claim that the remaining rising contribution is realised by equation
  `(3)` or `(4)` in source charts.
- No source-label legality, terminal `tilde t=0`, vector admissibility, chart
  sequence, Lemma 5 order count, pole order, normal crossings, or RLCT
  extraction.
