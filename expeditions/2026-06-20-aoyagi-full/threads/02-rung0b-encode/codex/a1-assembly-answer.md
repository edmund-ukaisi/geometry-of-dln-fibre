**Bridge A Recipe**

Use sorting, but hide it behind one wrapper. Do not try to feed positional `edgeQ` directly to `karamata_sq`; the positional prefix order is not the order Karamata wants.

Best route:

```lean
def sortAsc (v : Fin L → ℤ) : Fin L → ℤ :=
  v ∘ Tuple.sort v
```

Prove/apply a Fin-indexed wrapper:

```lean
karamata_sq_fin_unsorted
  (x y : Fin L → ℤ)
  (hy : Monotone y)
  (htot : ∑ i, x i = ∑ i, y i)
  (hpre : ∀ k (hk : k ≤ L),
    ∑ i : Fin k, sortAsc x (Fin.castLE hk i)
      ≤ ∑ i : Fin k, y (Fin.castLE hk i))
  :
  ∑ i, y i ^ 2 ≤ ∑ i, x i ^ 2
```

Internally apply your banked `karamata_sq` to `sortAsc x` and rewrite sums by permutation.

Mathlib names I am **CERTAIN** exist in v4.29 from the vendored source:

- `Tuple.sort`
- `Tuple.monotone_sort`
- `Tuple.comp_perm_comp_sort_eq_comp_sort`
- `Equiv.sum_comp`
- `Equiv.Perm.ofFn_comp_perm`
- `List.sortedLE_ofFn_iff`
- `Monotone.sortedLE_ofFn`
- `List.sublist_of_subperm_of_sortedLE`
- `List.sublist_iff_exists_fin_orderEmbedding_get_eq`
- `StrictMono.le_apply`
- `Finset.inf'_le`

For “sum of first `k` sorted entries ≤ any `k`-subsum”: I do **not** see this packaged as one Mathlib lemma. Bank it locally.

Recommended local lemma:

```lean
lemma sum_sortAsc_prefix_le_sum_subset
  (v : Fin L → ℤ) (s : Finset (Fin L)) :
  ∑ i : Fin s.card,
      sortAsc v (Fin.castLE (by simpa using s.card_le_univ) i)
    ≤ ∑ j in s, v j
```

Proof route: use `List.ofFn`, sort selected values, show it is a subperm/sublist of the full sorted value list via `List.sublist_of_subperm_of_sortedLE`, extract the order embedding with `List.sublist_iff_exists_fin_orderEmbedding_get_eq`, use `StrictMono.le_apply` to get indexwise comparison, then sum.

But this lemma alone is only an order-statistic tool. The real mathematical bridge should be a separate banked lemma:

```lean
QFeasible.sorted_prefix_le_target
  (hq : QFeasible M q) :
  ∀ k ≤ L,
    ∑ i : Fin k, sortAsc q (Fin.castLE ‹k ≤ L› i)
      ≤ ∑ i : Fin k, sortAsc targetY (Fin.castLE ‹k ≤ L› i)
```

That is the clean handoff to Karamata. Trying to derive it inline from the positional prefix bounds will be painful.

**Bridge B Verdict**

Use **B2**, not B1.

B1, proving `lambdaCore M = lambdaCore (sort M)` first, is high friction: `Adm` is positional, monotone in the original depth order, and not naturally transported by a permutation of widths. That proof is essentially another version of the theorem.

B2 should be structured as:

1. Define sorted target `y : Fin L → ℤ` from `β ++ tail`.
2. Prove a greedy/matching theorem:

```lean
exists_perm_target_QFeasible :
  ∃ π : Equiv.Perm (Fin L),
    QFeasible M (fun j => y (π j))
```

3. Use the formal inverse `QFeasible → Adm`:

```lean
QFeasible.exists_adm_edgeQ :
  QFeasible M q → ∃ T ∈ Adm M, ∀ j, edgeQ M T j = q j
```

4. Then:

```lean
∑ j, edgeQ M Tstar j ^ 2
= ∑ j, y j ^ 2
```

by `Equiv.sum_comp`.

5. Use `edge_identity` to convert the square-sum equality to `Mval`.
6. Use `Finset.inf'_le hTstar` for the upper bound.

For the clean-core match, avoid `cleanCore_perm` if possible by defining `targetY` from `sortedSmallest M c hc` from the start. Use `cleanCore_perm` only if your greedy construction produces the `c+1` small widths in an arbitrary order.

**Estimates / Recommendation**

Assuming your arithmetic facts are formal but not the two bridges:

- Bridge A wrapper + lower-bound assembly: ~80-140 lines.
- `sum_sortAsc_prefix_le_sum_subset`: ~70-120 lines.
- `QFeasible.sorted_prefix_le_target`: likely ~150-300 lines unless already mostly formal.
- Bridge B via B2: ~250-450 lines, mostly greedy placement plus `QFeasible → Adm`.
- B1: likely worse, ~400+ lines.

So the full close is probably **not** 150-250 more lines. It is more realistically **500-800** unless the QFeasible majorization and greedy achiever are already formal.

Recommendation: **STOP after banking Bridge A as a clean lower-bound theorem**, or even just bank `karamata_sq_fin_unsorted` plus `QFeasible.sorted_prefix_le_target` as named subgoals. Since this theorem is off the headline path, B2 is not worth opening unless the achiever construction becomes independently useful.