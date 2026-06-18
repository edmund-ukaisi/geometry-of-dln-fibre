**1. Recommended Split**

Use `codimForm_add`. Do not compute the full region `R`; prove these three exact local lemmas:

```lean
let δ := concatDelta (N := N) a b c d'
let M := extendℤ m

codimBil N M δ
  = - ∑ i ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ),
        ∑ j ∈ Finset.Icc (c : ℤ) (d' : ℤ),
          M (i - 1) (j - 1)

codimBil N δ M
  = - ∑ u ∈ Finset.Icc ((a : ℤ) + 1) (c : ℤ),
        ∑ v ∈ Finset.Icc (c : ℤ) (d' : ℤ),
          M u v

codimForm N δ = 1
```

Then bound the two rectangles by their source entries:

```lean
-M_rect₁ ≤ -M (a : ℤ) (b : ℤ)
-M_rect₂ ≤ -M (c : ℤ) (d' : ℤ)
```

using `Finset.single_le_sum` [SURE] twice and `Finset.sum_nonneg` [SURE], then `neg_le_neg` [SURE]. The source hypotheses give:

```lean
1 ≤ M (a : ℤ) (b : ℤ)
1 ≤ M (c : ℤ) (d' : ℤ)
```

via a small local lemma for `extendℤ` on `Fin` points, using existing `extendℤ_in_box`.

Final arithmetic:

```lean
codimBil N M δ + codimBil N δ M + codimForm N δ
  ≤ -M (a : ℤ) (b : ℤ) - M (c : ℤ) (d' : ℤ) + 1
  ≤ -1
```

Use `omega` [SURE] or `linarith` [SURE] for the final integer arithmetic.

**2. Collapsing `codimBil A δ`**

Recommended: expose δ as three point indicators, but put the singleton-sum pattern in a local helper. Use:

- `Finset.mul_sum` [SURE], often as `rw [← Finset.mul_sum]`
- `Finset.sum_sub_distrib` [SURE]
- `Finset.sum_add_distrib` [SURE]
- `Finset.sum_eq_single_of_mem` [SURE]
- `Finset.sum_eq_zero` [SURE]
- `Finset.mem_Icc` [SURE]
- `Finset.sum_congr` [SURE]
- `Finset.sum_filter` [SURE]

I would not rely only on raw `sum_ite_eq` simp. `Finset.sum_ite_eq` [SURE] and `Finset.sum_ite_eq'` [SURE] exist, but conjunctions like `u = a ∧ v = d'` make the orientation fiddly. A local helper based on `sum_eq_single_of_mem` is more stable.

**3. Collapsing `codimBil δ A`**

Do not globally reindex first. The first-factor support point `(α, β)` is read at:

```lean
i = α + 1
j = β + 1
```

Collapse in the actual nesting order:

1. Collapse outer `i` to `α + 1` with `Finset.sum_eq_single_of_mem` [SURE].
2. Inside the `u` sum, collapse `j` conditionally to `β + 1`.
3. Rewrite the remaining `u` range by `Finset.sum_filter` [SURE] and `Finset.mem_Icc` [SURE], with `omega`.

Important: if `β = d' = N`, then `j = d' + 1 = N + 1` is not in `Icc _ N`, so the `(a,d')` and `(c,d')` left-slot terms vanish. Handle this uniformly with a point-left lemma containing an `if β < N then ... else 0`, or split on `d' < N`.

**4. Direct Termwise Proof?**

Use the additive δ-expansion. A direct `Finset.sum_le_sum` termwise comparison is not cleaner, and the termwise inequality is not generally true before cancellations. It will just rederive the bilinear expansion inside the four nested sums.

Estimated Lean size: about 170-230 lines if you add reusable point/rectangle lemmas.

Subtasks:

1. Prove `extendℤ_fin_eq` and `extendℤ_nonneg`.
2. Prove right-slot rectangle identity for `codimBil N M δ`.
3. Prove left-slot rectangle identity for `codimBil N δ M`.
4. Prove `codimForm N δ = 1`.
5. Use `single_le_sum`/`sum_nonneg` to bound both rectangles.
6. Finish from `extendℤ_concatMove`, `codimForm_add`, and integer arithmetic.