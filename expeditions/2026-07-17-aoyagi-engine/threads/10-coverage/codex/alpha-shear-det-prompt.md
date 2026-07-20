# Lean 4 / Mathlib v4.29: cleanest route for the elementary Schur-shear Homeomorph + fderiv-det = 1

I need to formalise a small "source gauge" atom and want the cleanest Mathlib-v4.29 route (exact lemma
names + pitfalls), NOT full proofs.

## The object
Fix `d : ℕ` and distinct indices `a b c : Fin d` with `a ≠ b`, `a ≠ c`. Define the elementary shear
`f : (Fin d → ℝ) → (Fin d → ℝ)`,  `f x = Function.update x a (x a - x b * x c)`
(shift ONE coordinate `a` by minus the product of two OTHER coordinates `b`, `c`).

## What I need (two lemmas)
1. `f` is a `Homeomorph (Fin d → ℝ) (Fin d → ℝ)`. Its inverse is
   `g x = Function.update x a (x a + x b * x c)` (both polynomial, hence continuous).
2. At every point `x`, `f` has an fderiv whose determinant has absolute value 1
   (`|(fderiv ℝ f x).det| = 1`, or the ContinuousLinearMap/LinearMap `.det`). The derivative is
   `1 + (e_a ⊗ w)` where `w = -(x c) • e_b - (x b) • e_c` and `w a = 0`, so it's a rank-1 update of the
   identity with `det = 1 + w a = 1` (matrix determinant lemma).

## Questions
1. **Homeomorph construction (v4.29):** cleanest way to build the `Homeomorph` from an explicit two-sided
   inverse + continuity both ways? (`Homeomorph.mk` on an `Equiv` + `continuous_toFun`/`continuous_invFun`;
   how to discharge continuity of `x ↦ update x a (x a - x b * x c)` — does `fun_prop`/`by continuity`
   handle `Function.update` + coordinate projections? Is `continuous_apply`/`continuous_update` needed?)
2. **fderiv of the update-shear:** how to get `HasFDerivAt f L x` with an explicit `L`? The map is
   `update x a (x a - x b*x c)`; is there a clean way via `HasFDerivAt.update` /
   `hasFDerivAt_update` / `HasFDerivAt.pi` / componentwise (`hasFDerivAt_apply`)? What's the explicit `L`
   as a `ContinuousLinearMap`?
3. **det = 1 route:** given `L = ContinuousLinearMap.id + R` with `R` the rank-1 (or nilpotent, R²=0)
   perturbation, cleanest way to `|L.det| = 1`? Options: (a) `LinearMap.det` via nilpotence
   (`det (1 + N) = 1` for `N` nilpotent — is there a Mathlib lemma?); (b) convert to `Matrix` via
   `LinearMap.toMatrix (Pi.basisFun ℝ (Fin d))` and use the matrix determinant lemma
   `Matrix.det_one_add_col_mul_row` (exact name/signature at v4.29?) or `Matrix.det_updateRow_add_smul`;
   (c) show `L` is a product of transvections. Which is least painful? Give exact lemma names.
4. Any instance/diamond pitfalls for `det` on `(Fin d → ℝ) →L[ℝ] (Fin d → ℝ)` (the `Module`/`FiniteDimensional`
   instances, `ContinuousLinearMap.det` reducing to `LinearMap.det`)?
5. Is there an even simpler framing I'm missing (e.g. the shear as a `Homeomorph` whose Jacobian is
   MANIFESTLY 1 via a measure-preserving / `volume`-preserving Mathlib API, sidestepping the matrix det)?

Give the recommended route as a short lemma skeleton with the exact v4.29 lemma names at each step.
