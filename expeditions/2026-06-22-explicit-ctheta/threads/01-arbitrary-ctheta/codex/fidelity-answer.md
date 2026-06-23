1. **FACT:** no `Monotone d` hypothesis appears on the LHS vector in the four signatures. `1 ≤ N` is a size/nonemptiness condition, `∀ k, r ≤ d k` is rank feasibility, and `h` is Kostant-set nonemptiness; none imposes coordinate monotonicity. **INFERENCE:** the monotonicity is not smuggled onto `d`; it is used only after replacing `d` by its sorted representative.

2. **FACT:** Mathlib’s `Tuple.sort` satisfies `Tuple.monotone_sort : Monotone (d ∘ Tuple.sort d)`, and the local witness proves `![2,3,2] ∘ sort = ![2,2,3]`. So the RHS is genuinely the ascending sorted value tuple, with tie-breaking irrelevant because `cValue`/`cTheta` see the composed tuple. **INFERENCE:** this is not accidentally evaluating the unsorted vector.

3. **FACT:** the theorem names include `_comp_sort`, and the RHS visibly uses `cValue`/`cTheta` on the sorted vector, not on raw `d`. Calling it “Thm 7.10 for arbitrary d” is honest only as a permutation-invariance corollary: arbitrary `d` is computed by sorting first. It would be an overclaim if advertised as the original monotone-gated formula applied directly to non-monotone `d`.

4. **FACT:** the hypotheses are not weakest: for `r = 0`, `h` follows from `1 ≤ N`; for general `r`, `hN + hr` gives nonemptiness, while `h` itself also forces `hr`. They are not vacuity-inducing, though: for `N ≥ 1` and feasible `r`, the Kostant set is inhabited. `hr` is mathematically real rank-feasibility/proof infrastructure, but logically redundant if `h` is already assumed.

5. **FACT:** the remaining assumptions are `N ≥ 1`, feasible rank, permutation invariance, rank-shift, and correctness of the monotone closed forms. **INFERENCE:** the only fidelity caveat is wording: the closed form is on the sorted shifted representative, not the original order. No hidden monotonicity of the original dimension vector is present.

HONEST: explicit (C,θ) for arbitrary d