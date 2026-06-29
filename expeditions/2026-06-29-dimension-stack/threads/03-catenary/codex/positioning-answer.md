1. **Crux Verdict**

Re-expose the substitution. I do not see a public v4.29 route from `exists_integral_inj_algHom_of_quotient` to the needed one-variable monic-positioning automorphism; that theorem forgets exactly the tower/coordinate data your induction needs. A transdeg or affine-dimension-formula route would need substantially more public infrastructure and is not likely shorter than exposing the existing `T` argument. I would expose only the final lemma and keep the copied bookkeeping internal.

2. **Any Field**

Confirmed. The substitution is characteristic-free and field-cardinality-free: exponents live in `ℕ`, distinctness is base-expansion bookkeeping, and no generic scalar or `k`-point is chosen. Finite fields and positive characteristic should be fine. The real field use is that a nonzero coefficient of `f` is a unit, so the selected leading coefficient becomes a unit constant polynomial.

3. **Module Split**

The split is sane. Keep `ringKrullDim (R ⧸ p) = noetherRank` out of `Catenary`; that is Noether-normalization/dimension-invariance content, not catenarity. Putting the ring-general `A → A[X]` height-additivity brick in `Core.Dimension.Catenary` is fine: despite being more general than the field theorem, it is exactly the catenary infrastructure used by the peel step. If you want cleaner altitude, put it under a `PolynomialTower` section/namespace inside `Catenary`, but I would not create a separate module just for that unless reuse grows.