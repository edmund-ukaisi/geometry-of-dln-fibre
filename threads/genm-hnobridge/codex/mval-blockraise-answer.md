**Best Route**
This will work: among `(a)/(b)/(c)`, do `(a)` in spirit, but with Q3 as the actual collapse. First rewrite away `tPrev` via an auxiliary `u`-sequence (`u 0 = M 0`, `u (j+1) = T j`), then define `g` as “new summand minus old summand” and prove `∑ g = g (q-1)` by support. In pure Mathlib the clean collapse is `Finset.sum_eq_single_of_mem` on `Finset.range L` (or `Finset.sum_eq_single` on `Finset.univ : Finset (Fin L)`), with the usual `Finset.sum_sub_distrib`/`Finset.sum_congr`; `Finset.sum_filter` is optional, and `Fin.sum_univ_eq_sum_range` only matters if you still start from a `Fin L` sum. Yes: that support-collapse route is cleaner than an interval split; `(b)` is second-best, and `(c)` is not the right shape here. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/BigOperators.html))

**Boundary**
Don’t let `tPrev` survive into the main proof. Set `u_T 0 := M 0`, `u_T (j+1) := T j`, and `δ k := if q ≤ k ∧ k ≤ b-1 then (1 : ℤ) else 0`; prove `u_{T'} k = u_T k + δ k` for `k ≤ L`. Then each delta summand depends only on `u j`, `u (j+1)`, `δ j`, `δ (j+1)`, so the top boundary is just `δ (b-1)=1`, `δ b=0`. The `j=0` / `tPrev` branch is paid once, not inside the sum.

**Traps**
- For `q ≤ j ≤ b-2`, the delta is `-r_{j+1}` (equiv. `-r_s` with `s = j+1`), not `-r_{j+2}`.
- The bump block is `[q-1, b-2]`, but the affected summands are `[q-1, b-1]`; the extra `b-1` term comes from `tPrev`.
- At `j = q-1`, the new term is `(r_q - 1)(c_q - 1)`, so the delta is `1 - r_q - c_q`; the `+1` is real.
- At `j = b-1`, the delta is `+c_b`, not `-c_b`.
- `c_s ≥ 1` on `[q, b-1]` is not needed for the identity itself, only for admissibility / the final strict inequality.
- Keep block tests in `ℕ`; cast only values to `ℤ`. If you stay with `j.val - 1`, `q = 1` is the only real boundary nuisance.

**Arithmetic**
Write the `j`-summand as `F_j = (T(j+1) - T(j+2)) (M_{j+1} - T(j+2)) = r_{j+1} c_{j+1}`.

- `j = q-1`:
  `F'_j - F_j = (r_q - 1)(c_q - 1) - r_q c_q = 1 - r_q - c_q`.
- `q ≤ j ≤ b-2`, with `s := j+1 ∈ [q+1, b-1]`:
  `F'_j - F_j = r_s (c_s - 1) - r_s c_s = -r_s = 0`.
- `j = b-1`:
  `F'_j - F_j = (r_b + 1)c_b - r_b c_b = c_b = 0`.

So `Mval M T' - Mval M (tStar M) = 1 - r_q - c_q`.