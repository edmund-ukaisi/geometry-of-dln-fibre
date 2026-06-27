1. **VERDICT:** Sound, and close to the cleanest route. I would make two changes: do not split off the last variable, since `finSuccEquiv`/`eval_eq_eval_mv_eval'` are already aligned with `Fin.cons y s`; and do not define `T` as `e '' Z`, define it explicitly in the transported coordinates. Also skip a separate `n=1` case: base `n=0` plus the induction step covers it.

2. **Top Frictions, Ranked:**

1. **Product orientation.** Use
   `e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).trans MeasurableEquiv.prodComm`,
   so `e : (Fin (n+1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ`. Then `measure_prod_null_of_ae_null` slices over the first factor, namely `s : Fin n → ℝ`.

2. **Nonzero specialization.** Do not try `Polynomial.map_ne_zero_iff`; `eval s` is not injective. Use the leading coefficient of `q := finSuccEquiv ℝ n p`.

3. **Measurability of `T`.** This should be routine via `MvPolynomial.continuous_eval` and continuity of `(s,y) ↦ Fin.cons y s`; it is less conceptually dangerous than the previous two.

3. **Inductive Step Skeleton:**

Let

`T : Set ((Fin n → ℝ) × ℝ) := {z | MvPolynomial.eval (Fin.cons z.2 z.1) p = 0}`.

Then prove `Z = e ⁻¹' T` using `Fin.cons_self_tail` after unfolding `e`; use `MeasurePreserving.measure_preimage_equiv` for `e`. The measure-preserving proof is `volume_preserving_piFinSuccAbove ... 0` composed with `Measure.measurePreserving_swap`, with likely `rw [Measure.volume_eq_prod _ _]` to align target measures.

For slices:

- Fubini slices over `s : Fin n → ℝ`:
  `Prod.mk s ⁻¹' T = {y : ℝ | eval (Fin.cons y s) p = 0}`.

- Put `q := MvPolynomial.finSuccEquiv ℝ n p`.
  From `hp`, get `hq : q ≠ 0` by the alg-equivalence injectivity / `EmbeddingLike.map_ne_zero_iff`.

- Put `c := q.leadingCoeff`.
  Get `hc : c ≠ 0` from `Polynomial.leadingCoeff_ne_zero`.

- By IH, `volume {s | MvPolynomial.eval s c = 0} = 0`.
  Hence a.e. `s`, `eval s c ≠ 0`, using `ae_iff`.

- For such `s`, define `qs := q.map (MvPolynomial.eval s)`.
  Since `(MvPolynomial.eval s) c ≠ 0`, use `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero` or the equivalent `coeff_map` argument to prove `qs ≠ 0`.

- For that `s`, rewrite the slice by
  `MvPolynomial.eval_eq_eval_mv_eval' s y p`:
  `eval (Fin.cons y s) p = Polynomial.eval y qs`.

- Then
  `Polynomial.finite_setOf_isRoot hqs`
  gives finiteness of the slice, and
  `Set.Finite.measure_zero _ volume`
  gives `volume (Prod.mk s ⁻¹' T) = 0`.

Thus obtain
`(fun s => volume (Prod.mk s ⁻¹' T)) =ᵐ[volume] 0`,
and conclude with
`Measure.measure_prod_null_of_ae_null hT hslices`.

For `hT : MeasurableSet T`, use `MvPolynomial.continuous_eval` composed with the continuous map `(s,y) ↦ Fin.cons y s`, then `measurableSet_eq_fun` or closed-preimage of `{0}`.

4. **Lemma Notes:**

Verified locally/high confidence: `MeasurableEquiv.prodComm`, `Measure.measurePreserving_swap`, `Measure.volume_eq_prod`, `MvPolynomial.continuous_eval`, `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero`, `Polynomial.coeff_map`, `Fin.cons_self_tail`.

Do not rely on `Polynomial.map_ne_zero_iff` for the specialized univariate polynomial; it needs injectivity and is the wrong tool here.

`Measure.prod_apply_symm` exists, so you could keep the product as `ℝ × (Fin n → ℝ)` and slice symmetrically, but composing with `prodComm` is cleaner for `measure_prod_null_of_ae_null`.