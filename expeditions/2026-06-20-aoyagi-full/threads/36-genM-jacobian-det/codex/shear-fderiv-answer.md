**Q1.** There is no multivariate `HasFDerivAt.div` in Mathlib v4.29. Use multiplication plus composed inverse. Prefer the scalar-field lemma `hasFDerivAt_inv` from `Mathlib.Analysis.Calculus.Deriv.Inv`, because it gives a cleaner `toSpanSingleton` CLM than `hasFDerivAt_inv'`.

```lean
import Mathlib

noncomputable def ratio10Deriv (u : Fin 4 → ℝ) :
    (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (u 1) •
      (((ContinuousLinearMap.toSpanSingleton ℝ (-(u 0 ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 4))))
    + (u 0)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (1 : Fin 4)

theorem ratio10_hasFDerivAt {u : Fin 4 → ℝ} (hu : u 0 ≠ 0) :
    HasFDerivAt (fun y : Fin 4 → ℝ => y 1 / y 0) (ratio10Deriv u) u := by
  have h0 : HasFDerivAt (fun y : Fin 4 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 4)) u :=
    hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) u
  have h1 : HasFDerivAt (fun y : Fin 4 → ℝ => y 1)
      (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 4)) u :=
    hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) u
  have hinv : HasFDerivAt (fun y : Fin 4 → ℝ => (y 0)⁻¹)
      (((ContinuousLinearMap.toSpanSingleton ℝ (-(u 0 ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 4)))) u := by
    simpa using (hasFDerivAt_inv (𝕜 := ℝ) hu).comp u h0
  simpa [ratio10Deriv, div_eq_mul_inv] using h1.mul hinv
```

This `D` is:
```lean
v ↦ (u 1) * (-(u 0 ^ 2)⁻¹ * v 0) + (u 0)⁻¹ * v 1
```

If you insist on `hasFDerivAt_inv'`, the CLM produced is:

```lean
(u 1) •
    (((-ContinuousLinearMap.mulLeftRight ℝ ℝ (u 0)⁻¹ (u 0)⁻¹).comp
      (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 4))))
  + (u 0)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (1 : Fin 4)
```

**Q2.** The apply lemma is:

```lean
ContinuousLinearMap.mulLeftRight_apply
```

Use this simp block:

```lean
example (u v : Fin 4 → ℝ) :
    (((-ContinuousLinearMap.mulLeftRight ℝ ℝ (u 0)⁻¹ (u 0)⁻¹).comp
        (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 4))) v)
      = -((u 0)⁻¹ * (u 0)⁻¹ * v 0) := by
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.proj_apply]
  ring
```

For larger CLM equalities, use:

```lean
ext v
simp only [ContinuousLinearMap.comp_apply,
  ContinuousLinearMap.proj_apply,
  ContinuousLinearMap.add_apply,
  ContinuousLinearMap.sub_apply,
  ContinuousLinearMap.neg_apply,
  ContinuousLinearMap.smul_apply,
  ContinuousLinearMap.toSpanSingleton_apply,
  ContinuousLinearMap.mulLeftRight_apply]
field_simp [hu]
ring
```

**Q3.** Rank by v4.29 friction:

1. **Lowest friction for `shear121_hasFDerivAt`:** hand-written CLM/matrix plus `hasFDerivAt_pi''`, proving each component. Use `ratio10_hasFDerivAt` above, then for component `2` use `.mul` and `.sub`, and only match the single row `(proj 2).comp (shear121Deriv u)`, not the whole matrix CLM.

2. **Higher friction:** `fun_prop`/`DifferentiableAt`, then `fderiv`. There is a useful theorem:
   ```lean
   fderiv_pi
   ```
   but determinant computation still forces you to identify the resulting `fderiv` CLM with a concrete triangular/matrix CLM. So this route does not really avoid the matrix equality; it only postpones it.

**Q4.** Yes, a `MeasurePreserving` route can sidestep the fderiv/determinant route for the change of variables, provided you prove the shear is measure-preserving and have the right image/preimage form.

The relevant lemmas are:

```lean
MeasurePreserving.lintegral_comp
MeasurePreserving.lintegral_comp_emb
MeasurePreserving.setLIntegral_comp_preimage
MeasurePreserving.setLIntegral_comp_preimage_emb
MeasurePreserving.setLIntegral_comp_emb
```

For your image-form statement, the key one is:

```lean
(hmp.setLIntegral_comp_emb hφemb g (S \ N0)).symm
```

where `hmp : MeasurePreserving φ volume volume` and `hφemb : MeasurableEmbedding φ`.

To prove measure-preservation of this kind of shear, use:

```lean
MeasurePreserving.skew_product
measurePreserving_add_right
Measure.volume_eq_prod
```

This repo already has the same pattern in `measurePreserving_coreShear`, using `MeasurePreserving.skew_product`.

RECOMMEND: For a sorry-free `shear121_hasFDerivAt`, use Q1’s `hasFDerivAt_inv` + `.mul` componentwise, then `hasFDerivAt_pi''`, matching only the four scalar rows to the matrix CLM. For the downstream c-o-v with weight `1`, prefer the `MeasurePreserving.skew_product` route if you do not otherwise need the explicit Jacobian theorem.