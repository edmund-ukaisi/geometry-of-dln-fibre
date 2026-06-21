Use the **iterated node c-o-v**. It is shorter in Lean. Keep the composite `φ` only as notation.

Important: the leaf parametrisation should use `lemma2Inv`, not `lemma2Fwd`:
`φ u = step1A (cons (u 0) (lemma2Inv (step2E (tail u))))`,
because `step1Residual v = resolvedForm (lemma2Fwd v)`, so you need `lemma2Fwd v = step2E z`.

Do not prove one 8-by-8 composite determinant unless forced. Chain:
`step1A` gives `|Jac| = |y0|^3`, Lemma-2 gives `|Jac| = 1`, `step2E` gives `|Jac| = |z1|^2`. Use sure/local names:
`pivotBlowupOnDeriv_det` or `pivotBlowupDeriv_det`, `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, `measurePreserving_lemma2Hom`, `myF222_step1A`, `step1Residual_eq_resolvedForm`, `resolvedForm_step2E`.

For the lower bound, c-o-v gives an equality, and monotonicity gives the inequality:
```lean
have hmono :
  ∫⁻ x in φ '' V, g x ≤ ∫⁻ x in cubeBox 8 ε, g x :=
  lintegral_mono_set hVimage

have hcov :
  ∫⁻ x in φ '' V, g x
    = ∫⁻ u in V, ENNReal.ofReal |(φ' u).det| * g (φ u) :=
  lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hV hderiv hinj g
```
Then RHS `= ⊤` forces the cube integral `= ⊤` by `top_le_iff.mp` after rewriting. You may lower-bound the post-c-o-v integrand using `lintegral_mono_ae`, but you cannot omit the Jacobian term; it enters through the equality.

On the positive chart box, rewrite:
```lean
|det Dφ| * |myF222 (φ u)|^(-c')
= |y0|^3 * |z1|^2 * (|y0|^2 * |z1|^2 * |U u|)^(-c')
= (|y0|^3 * |z1|^2) * (|y0|^2 * |z1|^2)^(-c') * |U u|^(-c')
= monomialIntegrand 2 (![1,1]) (![3,2]) c' ![y0,z1] * |U u|^(-c')
```
Use `simp [monomialIntegrand, Fin.prod_univ_two]` plus `Real.mul_rpow`, `Real.rpow_natCast`, and positivity side conditions.

For the atom:
```lean
monomialIntegrand_lintegral_box_eq_top
  2 (![1,1]) (![3,2]) ⟨1, by norm_num⟩ (c' : ℝ)
```
with threshold closed by sure/local:
```lean
simpa [case222_unit_leaf_threshold] using hgt.le
```

Soundness flags:

- `U ≥ 1` alone is not enough for divergence; since exponent is negative it gives an upper bound. On the chosen bounded box also prove `U ≤ B`, then either lower-bound by `B^(-c')` or use `integrableOn_monomial_mul_unit_iff` by contradiction.
- A 2D slice is measure zero. Either add a Fubini/spectator product step (`setLIntegral_prod`, `lintegral_const_mul`, `lintegral_mul_const`) for the six remaining variables, or formulate the atom in `d = 8` with zero `k,h` on spectators.
- `InjOn` fails on pivot-zero loci if `V` includes `y0=0` or `z1=0`; use `V \ Z` or positive boxes.
- Prove `φ '' V ⊆ cubeBox 8 ε` by choosing a small box radius after Lemma-2 polynomial bounds. This is real bookkeeping, not automatic.