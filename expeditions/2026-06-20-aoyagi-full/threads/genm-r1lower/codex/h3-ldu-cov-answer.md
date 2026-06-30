**1. VERDICT**

NO. `interiorLDU_cov` is not provable sorry-free from `{R1, R2, R3}` alone.

**2. WHY**

The target is a genuine image-pushforward change-of-variables identity for arbitrary `g : E → ℝ≥0∞`:

```lean
∫⁻ x in φ '' S, g x = ∫⁻ u in S, jac u * g (φ u)
```

Without injectivity, the RHS counts preimages with multiplicity while the LHS integrates over the image once. The non-injective version would need a multiplicity/area-formula term or an a.e.-injectivity hypothesis. R1 only identifies the numeric value of `|det (fderiv ℝ φ u)|`; since `fderiv` is defined even when `φ` is not differentiable, it does not supply `HasFDerivWithinAt`/`Differentiable`.

The Mathlib route I know exists in v4.29 is exactly:

```lean
lintegral_image_eq_lintegral_abs_det_fderiv_mul
```

and the local uses show it needs:

```lean
MeasurableSet s
∀ x ∈ s, HasFDerivWithinAt f (f' x) s x
Set.InjOn f s
```

There is no available Mathlib v4.29 theorem, in this project surface, that proves this exact image identity from only a determinant-value equality plus source null hyperplanes. R2 helps remove source coordinate slices, but it does not supply injectivity, differentiability, or image-null control for arbitrary `φ`.

**3. RECOMMENDATION**

Surface a WALL. The frozen signature is under-resourced: a sorry-free close needs differentiability and injectivity/a.e.-injectivity facts for `interiorLDUphi` on the relevant punctured set, plus the usual null-slice bookkeeping. If H1 owns the factor-list/map-equality route that can produce those facts, this theorem should wait for H1 or for another sub-task to bank the missing `HasFDerivWithinAt` and `InjOn` facts.