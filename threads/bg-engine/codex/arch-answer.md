1. **Representation**

Decision: use the count/filter characterization as the internal `Dom`.

Define `c_M(τ) := (M.filter (fun x => x < τ)).card`. Use
`DomC B R := R.card = B.card ∧ ∀ τ, c_R(τ) ≤ c_B(τ)`.

Mathematically certain: with equal cardinalities over a linear order, this is equivalent to sorted pointwise domination. If sorted `rᵢ ≥ bᵢ`, then fewer `R` elements can lie below any threshold. Conversely, if some first/any index has `rᵢ < bᵢ`, take `τ = bᵢ`; then `R` has at least `i+1` elements `< τ`, while `B` has at most `i`, contradiction. Do not use Mathlib’s `Multiset` order for this; that is submultiset/multiplicity inclusion, not stochastic/sorted domination.

2. **ENGINE-2 Closure**

Let `B := b.toMultiset`, `t ∈ B`, and choose `v ∈ R` minimal with `t ≤ v`. Existence: if no `R` element is `≥ t`, then every `R` element is `< t`, so `c_R(t)=n`; but `t ∈ B`, so `c_B(t)<n`, contradicting `c_R(t)≤c_B(t)`.

For closure, prove for every threshold `τ`:
`c_{R.erase v}(τ) ≤ c_{B.erase t}(τ)`.

Use:
`c_{R.erase v}(τ)=c_R(τ)-[v<τ]`,
`c_{B.erase t}(τ)=c_B(τ)-[t<τ]`.

Cases:

- `τ ≤ t`: then `v<τ` and `t<τ` are false. Need `c_R(τ)≤c_B(τ)`, exactly Dom.

- `t < τ ≤ v`: then `t<τ` true, `v<τ` false. Minimality gives no `R` element in `[t,v)`, hence no `R` element in `[t,τ)`, so `c_R(τ)=c_R(t)`. Also `t ∈ B` and `t<τ`, so `c_B(t)+1≤c_B(τ)`. Chain:
  `c_{R.erase v}(τ)=c_R(τ)=c_R(t)≤c_B(t)≤c_B(τ)-1=c_{B.erase t}(τ)`.

- `v < τ`: then both indicators are `1`. From `c_R(τ)≤c_B(τ)`, subtract one on both sides:
  `c_R(τ)-1≤c_B(τ)-1`.

This is exactly where count-form pays off.

3. **ENGINE-1(c)**

IH for the recursive call should be:

For `b' := b.dropLast`, `R' := R.erase v`, `q' := greedy b' R'`, for every list `s` with `s.toMultiset = R'` and `∀ i, b'[i]≤s[i]`, and every suffix index `j`,  
`Suffix(q',j) ≤ Suffix(s,j)`.

For a competitor `p` for `(b,R)`, write `u := p.last`, `p' := p.dropLast`. Feasibility gives `t≤u`, and `u∈R`, so minimality gives `v≤u`.

Subtle point: IH does not apply directly to `p'`, since `p'.toMultiset = R.erase u`, not necessarily `R.erase v`. If `u≠v`, replace one occurrence of `v` in `p'` by `u`; call the result `p♯`. Then `p♯.toMultiset = R.erase v`, and feasibility is preserved because the replaced entry only increases. If `u=v`, take `p♯=p'`.

Now `q = q' ++ [v]`, `p = p' ++ [u]`.

For the last suffix: `v≤u`.

For `j < b'.length`:
`Suffix(q,j)=Suffix(q',j)+v`
`≤ Suffix(p♯,j)+v` by IH.

If the replacement position `k` is outside the suffix (`k<j`), then `Suffix(p♯,j)=Suffix(p',j)`, so add `v≤u`. If `k` is inside (`j≤k`), then `Suffix(p♯,j)=Suffix(p',j)+(u-v)`, so adding `v` gives equality with `Suffix(p',j)+u`. Thus always:
`Suffix(q,j) ≤ Suffix(p',j)+u = Suffix(p,j)`.

4. **Mathlib Leads**

Confirmed broad API surface: `Multiset.sort`, `coe_sort`, `sort_eq`, `pairwise_sort`, `length_sort`, `mem_sort`; `List.sortedLE_mergeSort`, `List.pairwise_mergeSort'`, `List.sortedLE_iff_monotone_get`, `List.SortedLE.monotone_get`. Verify exact v4.29 names locally. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Sort.html))

Verify names: `Multiset.le_iff_count` or nearby count characterization for submultiset order; useful only as a multiplicity helper, not as Dom. Docs confirm `Multiset ≤` is sublist/up-to-permutation, equivalently pointwise multiplicity count. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Defs.html))

Verify names: `filter_erase`, `erase_filter`, `card_erase_of_mem`, `count_erase`. If awkward, prove one local lemma for `card ((M.erase a).filter P)` by cases on `P a`.

For `find?`, verify names like `List.find?_some` / `find?_eq_some`; otherwise prove a tiny sorted-list lemma: first element satisfying `t≤x` is minimal among satisfying members.