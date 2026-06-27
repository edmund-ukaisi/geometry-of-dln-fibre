1. SCOPE VERDICT

(c) the statement as written is the wrong Lean target.

Keep this theorem as the final wrapper, but prove a better-factored core: a finite-dimensional raw `frobSq` comparison for block shears with entrywise shear bounds `|B₁ a b| ≤ 1`, `|B₂ a b| ≤ 1`, plus separate Schur determinant/block identity and Cramer shear lemmas. The full general-r theorem is mathematically fine, but proving constants, Cramer ratios, block indexing, and Schur identities all inside one statement will be a slog. The wrapper should assemble pre-staged lemmas; N4 only needs the two-sided threshold equivalence, not the monolithic matrix-analysis certificate.

2. THE c₀/c₁ CONSTRUCTION

Rank: (ii) raw `frobSq` entrywise proof is much more Lean-tractable than (i).

Avoid `opNorm`/`frobenius_norm`: they introduce normed-space coercions, matrix-as-linear-map transport, and equivalence between Mathlib Frobenius and your raw sum. Instead prove explicit finite-sum inequalities:

- `frobSq_add_le`: `frobSq (X + Y) ≤ 2 * (frobSq X + frobSq Y)`.
- `frobSq_mul_entryBound_le`: if `∀ i k, |A i k| ≤ C`, then `frobSq (A * B) ≤ n * C^2 * frobSq B`, using Cauchy-Schwarz on each row.
- `frobSq_shear_le`: for shear `P + B Q`, bound by an explicit polynomial in `j`, `r-j`.
- reverse direction by applying the inverse shear, whose entries also satisfy the same bound.

Load-bearing lemmas for winner: `Finset.sum_nonneg` [LIKELY-EXISTS], `Finset.sum_le_sum` [LIKELY-EXISTS], `sq_nonneg` [LIKELY-EXISTS], `abs_mul` [LIKELY-EXISTS], `sq_abs` [INFER], `Real.sq_le_sq` / `sq_le_sq` verify exists, `Finset.sum_mul` / `Finset.mul_sum` [LIKELY-EXISTS], and Cauchy-Schwarz: search `Finset.sum_mul_sq_le_sq_mul_sq` or `inner_le_norm` if using Euclidean vectors [INFER]. If that lemma is annoying, prove the elementary finite Cauchy-Schwarz once as a local lemma.

3. THE SHEAR BOUND

This is the real Lean long-pole; stage it as its own lemma.

Exact chain for `|(M21 * M11⁻¹) a b| ≤ 1`:

1. Expand inverse:
   `M11⁻¹ = (M11.det)⁻¹ • M11.adjugate` via `Matrix.inv_def` [INFER].
2. Rewrite entry:
   `(M21 * M11⁻¹) a b = (M11.det)⁻¹ * ∑ k, M21 a k * M11.adjugate k b`.
3. Identify the numerator as a determinant of `M11` with one row replaced by the corresponding lower row of `R`. This is the row-version analogue of Cramer.
4. Use determinant row expansion / adjugate identity to prove:
   `∑ k, row k * adjugate k b = det (replaceRow M11 b row)` up to transpose/sign depending on conventions.
5. Convert `replaceRow M11 b row` into `(R.submatrix I J)` for suitable `I J : Fin j → Fin r`.
6. Apply `hpivot` to get `|numerator| ≤ |M11.det|`.
7. Since `M11.det ≠ 0`, divide:
   `|numerator / M11.det| ≤ 1`.

For the right shear `M11⁻¹ * M12`, use the column version, much closer to `Matrix.cramer_apply` [INFER]: numerator is `det (M11.updateCol b col)`. For the left shear, either transpose and reuse column Cramer, or prove a row-update version via transpose. Search terms: `Matrix.inv_def`, `Matrix.adjugate`, `Matrix.cramer_apply`, `updateCol`, `updateRow`, `det_updateColumn`, `det_updateRow`.

4. CHEAPEST FIRST MILESTONE

Land the standalone shear lemma first:

```lean
lemma schur_left_right_shear_entry_le_one
  ... :
  (∀ a b, |(M21 * M11⁻¹) a b| ≤ 1) ∧
  (∀ a b, |(M11⁻¹ * M12) a b| ≤ 1)
```

with only `hpivot` and `M11.det ≠ 0` as serious hypotheses.

That de-risks the whole proof: once the shears are bounded, the norm comparison is elementary finite-sum algebra. A `j = 1` case is also useful, but it does not solve the adjugate/minor bookkeeping that general `j` needs.

5. TRAPS

1. `Matrix.submatrix` index maps: composing block inclusions into `Fin r` will dominate the Cramer proof. Treat maps like `top : Fin j → Fin r`, `bot : Fin (r-j) → Fin r` as named definitions, not inline lambdas.

2. `Fin (r-j)` arithmetic: every bottom index needs offset coercions and `omega`/`fin_cases` support. Predefine `botIndex : Fin (r-j) → Fin r`; do not repeatedly rebuild proofs.

3. Raw `frobSq` vs Mathlib Frobenius: mixing them will create coercion noise. Inference: stay raw until the theorem is done.

4. Block inverse/determinant identities: Mathlib block matrix lemmas may not line up with your `Fin j`/`Fin (r-j)` decomposition. Treat Schur determinant identity as a separate pre-staged lemma; verify names before relying on any `fromBlocks`/`toBlock` API.