codex (static_count smallestK route)
**Static Argument**
- Set `m := cLt(Ymulti, τ)` and rewrite it with `cLt_ofFn` as the cardinality of `{k : Yvec k < τ}`; the β–block enumeration gives `m ≤ c`.  
- Each element of that set is `< τ`, so the sum of the `m` smallest targets equals `smallestK L m Yvec` and is `< m·τ`. Combine this upper bound with `Yvec_lowerfit` to obtain `smallestK L m Yvec ≤ Sprefix(m+1) < m·τ`.  
- Apply `good_floor_core` at the same index `m` to translate the prefix inequality into an order-statistic inequality on the sorted widths: `aS_m < τ`. Via `aS_succ_le_Yvec` the same bound transfers to the sorted suffix `sortedWs := (ws_i).sort`, giving `aS_m ≤ sortedWs_{m-1} < τ`.  
- Because `cLt` is permutation-invariant, `cLt(ws_i, τ) = cLt(sortedWs, τ)`. The previous bullet shows that the `m`-th entry of `sortedWs` is already `< τ`, so the count of suffix elements below `τ` is at least `m`. Therefore `cLt(Ymulti, τ) = m ≤ cLt(ws_i, τ)` with no reliance on mixed strictness.

**Positional Suffix**
- The obstruction disappears after sorting the suffix: `sortedWs` is exactly the sorted multiset of `ws_i`, so `cLt(ws_i, τ) = cLt(sortedWs, τ)` by permutation invariance (`cLt_mono`). All “sorted-versus-positional” reasoning can be carried out on `sortedWs`, and the final inequality automatically re-descends to the original positional suffix.

**SmallestK Route**
- The smallestK chain above is uniform: `m` small targets ⇒ `smallestK L m Yvec < m·τ` ⇒ `Sprefix(m+1) < m·τ` (via `Yvec_lowerfit`) ⇒ `aS_m < τ` (`good_floor_core`). With `aS_succ_le_Yvec` relating the sorted widths and `sortedWs`, this forces the `m`-th suffix order statistic below `τ`, hence `cLt(ws_i, τ) ≥ m`. No ancillary case analysis on the tail is needed; all 13 332 Region‑A instances fall under the same algebraic comparison.

**Gaps**
- Every step is covered by the listed green lemmas; no hidden case split remains. The argument uses only the β-block enumeration, `cLt_ofFn`, `Yvec_lowerfit`, `good_floor_core`, `aS_succ_le_Yvec`, and permutation invariance of `cLt`.
