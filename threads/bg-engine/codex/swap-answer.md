DECISION: Route 2 explicit swap; route 1 only hides the same exchange and is not inductively cleaner.

The one-step helper I would prove is:

```lean
lemma swapForIH
  (hne : u ≠ v)
  (hp' : (p' : Multiset ℤ) = R.erase u)
  (huR : u ∈ R) (hvR : v ∈ R) (huv : v ≤ u)
  (hfeas : Feasible b' p') :
  let k := p'.idxOf v
  let p♯ := p'.set k u
  (p♯ : Multiset ℤ) = R.erase v ∧
  Feasible b' p♯ ∧
  ∀ j, (p♯.drop j).sum + v ≤ (p'.drop j).sum + u
```

Mathematically certain: in the `u ≠ v` case, `v ∈ p'` because `v ∈ R.erase u`; replacing that occurrence by the larger `u` preserves feasibility and gives the suffix inequality. If the changed index is outside the suffix, use `v ≤ u`; if inside, the suffix sum increases by exactly `u - v`.

Do not use an existential `Perm` construction: suffix sums depend on position, so you will immediately need a witness index anyway. `p'.set (p'.idxOf v) u` is the least painful encoding.

Main induction:

Base `b=[]`: use length/card from `(p : Multiset ℤ)=R` and `Dom [] R`; both suffixes are empty.

Step `b=b'++[a]`. Let `v := pick a R`, `q' := backwardGreedy b' (R.erase v)`, so `q=q'++[v]` using your recursion equation and `engine2_closure`.

For competitor `p`, get `p≠[]`, set `u := p.getLast _`, `p' := p.dropLast`, and rewrite `p=p'++[u]`. Feasibility gives `a ≤ u`; membership gives `u∈R`; pick-minimality gives `v≤u`.

If `u=v`, apply IH directly to `p'`.

If `u≠v`, build `p♯` by `swapForIH`, apply IH to `p♯`, then combine:
`q'.drop j.sum ≤ p♯.drop j.sum`
and
`p♯.drop j.sum + v ≤ p'.drop j.sum + u`.

Suffix splice: let `n=b.length`.

For `j < n`, have `j ≤ q'.length` and `j ≤ p'.length`, so
```lean
(q' ++ [v]).drop j = q'.drop j ++ [v]
(p' ++ [u]).drop j = p'.drop j ++ [u]
```
then `sum_append` and `sum_singleton`.

For `n ≤ j`, both full lists have length `n`, so both drops are `[]`; prove by `List.drop_eq_nil_of_le`.

Useful verified names: `List.drop_append_of_le_length`, `List.drop_eq_nil_of_le`, `List.sum_append`, `List.sum_singleton`, `List.dropLast_append_getLast`, `List.getLast_mem`, `List.idxOf_lt_length_of_mem`, `List.getElem_idxOf`, `List.set_eq_take_cons_drop`, `List.length_set`, `List.getElem_set`, `List.drop_set`, `List.sum_set`, `Multiset.mem_coe`, `Multiset.mem_erase_of_ne`, `Multiset.erase_comm`, `Multiset.cons_erase`, `Multiset.coe_eq_coe`, `List.Perm.sum_eq`.