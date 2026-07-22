## 1. Verdict

Viable, but unnecessarily expensive. The hidden cost is formalising inversion count and proving the one-step decrease.

Mathlib v4.29 does have the exact adjacent-generation result:

```lean
Equiv.Perm.mclosure_swap_castSucc_succ
```

from `Mathlib.GroupTheory.Perm.Sign`. I type-checked the following route in this worktree:

```lean
H := {σ | ∀ M, positive M →
  Nonempty (bindingSet M ≃o bindingSet (M ∘ σ))}
```

Show `H` is a submonoid using `OrderIso.refl` and `OrderIso.trans`; `swapBinding_orderIso` puts every adjacent swap in `H`; then

```lean
rw [Equiv.Perm.mclosure_swap_castSucc_succ]
```

shows every permutation—and hence `Tuple.sort M`—belongs to `H`. This is cleaner than inversion recursion, insertion sort, or extracting a factor list.

## 2. Key sublemmas

- Adjacent descent: build it; easy. Use

  ```lean
  Fin.monotone_iff_le_succ
  ```

  Thus `¬ Monotone M` gives some `k : Fin L` with
  `M k.succ < M k.castSucc`. `Tuple.sort_eq_refl_iff_monotone` connects this to sortedness. `Tuple.antitone_pair_of_not_sorted` only supplies an arbitrary inverted pair.

- Inversion decrease: build it; medium, index-heavy. I found no value-tuple inversion-count API. One must partition pairs into those disjoint from `{k,k+1}`, the swapped pair itself, and pairs involving one of those indices. Only `(k,k+1)` changes the total. This is the genuine difficulty hidden by the recursion.

- Sorted endpoint: do not formalise “same multiset”. Use the exact lemma

  ```lean
  Tuple.comp_perm_comp_sort_eq_comp_sort
  ```

  which gives

  ```lean
  (M ∘ σ) ∘ Tuple.sort (M ∘ σ) = M ∘ Tuple.sort M
  ```

  Alternatively use `Tuple.unique_monotone`. These eliminate the proposed final multiset argument entirely.

## 3. Fin/dependent-type hazards

`Fin (L+1)` remains fixed, so there is no changing index type. The changing subtype `↥(bindingSet M)` is handled by exact endpoint equalities.

Watch:

- preserve positivity under permutation:
  `fun s ↦ hpos (σ s)`;
- keep the recursive/intermediate width syntactically as `swapWidths k M`;
- multiplication orientation:

  ```lean
  M ∘ ⇑(a * b) = (M ∘ ⇑a) ∘ ⇑b
  ```

  using `Equiv.Perm.coe_mul`, matching `ea.trans eb`;
- simplify the final endpoint with
  `simp [sortedWidths, shiftedSorted]`, using local `dminus_zero`.

The closure proof also handles `L = 0` without a special branch.

## 4. Shortcut

Yes: the submonoid-closure proof avoids constructing any adjacent decomposition or sorting trace. It still derives arbitrary-permutation covariance from adjacent transports, rather than providing a new direct profile map.

A literal joint permutation `T ↦ T ∘ σ` is unavailable: widths use `Fin (L+1)`, profiles use `Fin L`, and admissibility depends on chain adjacency. With the current nonlinear, neighbor-dependent `swapR`, arbitrary covariance is naturally obtained by composition of adjacent transports.