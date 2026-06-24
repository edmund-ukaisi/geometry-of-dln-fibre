# Reproduction - Definition 3 all-source strict rank-width

Date: 2026-06-24.

Status: xhigh reviewed; formalised.

## Question

The all-source Definition 3 constructor assumes the strict selected inequality
for every source-range reduced width:

```text
L * M^(s) < sum_{j=1}^{L+1} M^(j).
```

The downstream ceiling-data package currently also asks separately for
rank-width nonnegativity, `r <= H(s)`, so that `M^(s)=H(s)-r` can be rewritten
as a natural subtraction.  This slice checks whether the all-source strict
inequalities already imply that rank-width hypothesis.

## Source Anchors

Aoyagi Definition 3 on PDF pp. 8-9 defines

```text
M^(s) = H^(s) - r
```

and, for selected values, requires

```text
sum_k M^(S_k) > ell * M^(s).
```

In the all-source branch, `ell=L` and every source index is selected, so this
becomes the displayed all-source strict inequality above.

## Pen-and-paper Calculation

Write

```text
f_s = M^(s),              T = sum_{j=1}^{L+1} f_j.
```

Fix an index `i`.  Assume `0 < L` and

```text
L * f_s < T
```

for every source index `s`.  Sum these inequalities over the `L` indices
other than `i`:

```text
sum_{s != i} L * f_s < sum_{s != i} T.
```

The left side is

```text
L * sum_{s != i} f_s,
```

and the right side is `L*T` because there are exactly `L` other indices.  Since
`0<L`, cancel `L`:

```text
sum_{s != i} f_s < T.
```

But

```text
T = f_i + sum_{s != i} f_s,
```

so

```text
0 < f_i.
```

Thus every reduced width is positive.  Since

```text
f_i = (H(i) : Int) - (r : Int),
```

positivity gives `r < H(i)`, hence the weaker rank-width hypothesis
`r <= H(i)`.

## Lean Shape

Add in namespace `AoyagiDefinition3SourceData`:

```text
sourceRangeRankWidth_of_all_selected_strict
```

with statement:

```text
theorem sourceRangeRankWidth_of_all_selected_strict
    {L : Nat} {H : Nat -> Nat} {r : Nat}
    (hL : 0 < L)
    (hstrict :
      forall s : Nat, 1 <= s -> s <= L + 1 ->
        (L : Int) * aoyagiReducedWidthInt H r s <
          sum j : Fin (L + 1), aoyagiReducedWidthInt H r (j.val + 1)) :
    forall s : Nat, 1 <= s -> s <= L + 1 -> r <= H s
```

Then add a package wrapper

```text
exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict
```

that has the same output as the existing `_rankWidth` theorem but removes the
explicit `hr` argument by using the new rank-width consequence.

## Nonclaims

- No arbitrary selected-cutpoint or Definition 3 source-data existence.
- No classification of Definition 3.
- No computation of `ceilWidth` or `aParam`.
- No branch-selection convention beyond the explicitly all-source branch.
- No Eq5 payload, chart production, normal crossings, pole order, or RLCT
  extraction.
