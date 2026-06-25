# Reproduction - Theorem 2 selected-width pair sum range/Icc form

Date: 2026-06-25.

Status: controller pen-and-paper reproduction before Lean.  This is finite
indexing arithmetic only.

## Source Anchor

Aoyagi Theorem 2, PDF p. 9, includes the pair sum

```text
sum_{1 <= i < j <= ell+1} M^(S_i) M^(S_j).
```

The existing Lean notation layer stores the selected widths as an indexed
family

```text
m : Fin (ell + 1) -> Int
```

and defines the pair sum by summing over all finite index pairs with an
indicator for `i.val < j.val`.

## Pen-And-Paper Check

Let

```text
w_i = m_i,     0 <= i <= ell.
```

The source pair sum is over exactly the strict upper-triangle index set

```text
{(i,j) : 0 <= i <= ell, 0 <= j <= ell, i < j}.
```

For a fixed `i`, the allowed `j` are precisely

```text
i+1 <= j <= ell.
```

Therefore

```text
sum_{0 <= i <= ell} sum_{0 <= j <= ell} [i < j] w_i w_j
  =
sum_{i=0}^{ell} sum_{j=i+1}^{ell} w_i w_j.
```

In Lean, the right-hand side is written with `Finset.range (ell + 1)` for
`0 <= i <= ell`, `Finset.Icc (i + 1) ell` for the inner range, and the total
accessor

```text
aoyagiSelectedWidthNat ell m i
```

for selected widths indexed by natural numbers.  On the range
`i < ell + 1`, this accessor simp-rewrites to the original finite-indexed
value `m <i>` by `aoyagiSelectedWidthNat_of_lt`.

## Lean Target

The theorem added to `FinalFormula.lean` is:

```text
aoyagiSelectedWidthPairSum_eq_range_Icc_selectedWidthNat
```

It proves:

```text
aoyagiSelectedWidthPairSum ell m =
  sum i in range (ell+1), sum j in Icc (i+1) ell,
    aoyagiSelectedWidthNat ell m i *
    aoyagiSelectedWidthNat ell m j.
```

The proof is the finite reindexing above:

1. Replace finite-indexed selected widths by the Nat accessor on finite
   values using `i.isLt`.
2. Rewrite the outer and inner finite sums with `Fin.sum_univ_eq_sum_range`.
3. Collapse the inner filtered range `{j < ell+1 | i < j}` to
   `Icc (i+1) ell` by arithmetic.

## Nonclaims

- No Definition 3 source-data existence.
- No branch selection or tie-breaker.
- No use of the corrected `paperEll` cutoff.
- No normal-crossing, pole-order, or RLCT extraction.
- No comparison with Core/LR `cValue`, `cTheta`, fibre codimension, or quiver
  geometry.
