**Cleanest Route**

1. **Best route: exploit the existential directly.**
   Prove only that the integer
   ```lean
   z := (Adm M).inf' (Adm_nonempty M) (Mval M) : ℤ
   ```
   is nonnegative. Then choose
   ```lean
   ℓ = 1
   m : Fin 2 → ℕ := ![1, z.toNat]
   ```
   because
   ```text
   cleanCore 1 (1,n) = n / 2
   ```
   for every `n : ℕ`. Since `lambdaCore M = z / 2`, this proves the frozen theorem.

   This completely avoids Def-3, sorting, balanced-split optimality, and the actual minimizer.

   Rough proof surface: **50-100 Lean lines**, mostly `Mval_nonneg_of_mem_Adm`.

   Known local/Mathlib API:
   - `Finset.le_inf'`, `Finset.le_inf'_iff`
   - `Finset.sum_nonneg`
   - `mul_nonneg`, `sub_nonneg.mpr`
   - `Int.natCast_toNat_eq_self.mpr` or `Int.toNat_of_nonneg`
   - `Fin.sum_univ_one`, `Fin.sum_univ_two`
   - `Nat.mod_one`, `Nat.div_one`, `ring_nf`/`ring`

2. **Slightly worse variant: use an actual argmin from `inf'`.**
   Use
   ```lean
   Finset.exists_mem_eq_inf'
   ```
   to get `T₀ ∈ Adm M` with `inf' = Mval M T₀`, prove `0 ≤ Mval M T₀`, then again choose `ℓ=1`, `m=(1, Mval M T₀)`.
   This is mathematically equivalent but adds witness bookkeeping.

   Rough proof surface: **70-120 lines**.

3. **Semantic Aoyagi/Def-3 route.**
   This is only needed if you strengthen the theorem to say that `(ℓ,m)` are the Def-3 selected widths, or at least come from `M`.

   Minimal decomposition:
   - define/encode the selected `ℓ+1` smallest widths;
   - prove balanced split minimizes `∑ qᵢ²` under fixed sum;
   - reparametrize `Adm` and telescope `Mval`;
   - prove lower bound for all admissible `T`;
   - construct the genuine minimizer and prove membership;
   - assemble with `Finset.le_inf'` and `Finset.inf'_le`.

   Rough proof surface: **200+ lines**, likely more if sorting/multiset selection is not already built.

   For balanced split: I did not find a direct Mathlib theorem. The clean local route is to prove it via square deviations:
   ```text
   P = ℓ d + a,
   qᵢ = d + uᵢ,
   ∑ uᵢ = a,
   ∑ uᵢ² ≥ a.
   ```
   The repo already has related local integer-square lemmas in `DLNFibre.Core.CThetaExplicit`, especially `abs_le_sumSq` / `isLeast_sumSq`.

**Crucial Answer**

Yes: route **(b)** is much cleaner. Since `cleanCore 1 (1,n) = n/2`, `cleanCore` represents every nonnegative half-integer. So you can match `½·min` directly by setting `n` to the nonnegative integer minimum. No Def-3 sort, no minimizer formula, no exchange proof.

This proves the exact frozen statement, but it also shows the statement is mathematically weak: it does not force the clean form to use widths related to `M`.

**Most Error-Prone Lean Step**

Not `inf'`; the risky part is proving `Mval_nonneg_of_mem_Adm`.

Dodge it by making two small API lemmas first:

```text
T ∈ Adm M → (T j : ℤ) ≤ tPrev M T j
T ∈ Adm M → (T j : ℤ) ≤ (M j.succ : ℤ)
```

Then `Mval_nonneg_of_mem_Adm` is just `sum_nonneg` plus `mul_nonneg` of two `sub_nonneg.mpr` terms. This keeps the `j.val = 0` / predecessor `Fin` case split isolated.