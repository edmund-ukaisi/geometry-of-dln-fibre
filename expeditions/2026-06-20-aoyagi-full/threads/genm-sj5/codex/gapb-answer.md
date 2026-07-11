## Q1

### Ranked routes

1. **CFC square-root route — recommended; verified against v4.29.**
2. **Direct `1 ≤ det (1 + C)` API — no such matrix lemma found**, but it is a short local spectral-theorem lemma.
3. **Weyl/eigenvalue monotonicity — unavailable.** `Matrix.IsHermitian.eigenvalues₀_antitone` only says eigenvalues are sorted by index; it is not Loewner monotonicity.

There is no `Matrix.PosSemidef.sqrt`. The confirmed v4.29 API is:

- `CFC.sqrt`
- `CFC.sqrt_nonneg`
- `CFC.sqrt_mul_sqrt_self`
- `CFC.sq_sqrt`
- `CFC.isUnit_sqrt_iff`
- `Matrix.PosSemidef.inv_sqrt`
- `Matrix.PosDef.posDef_sqrt` exists but is deprecated; prefer `CFC.isUnit_sqrt_iff` or `IsStrictlyPositive.sqrt`.

Import `Mathlib.Analysis.Matrix.Order` and `open scoped MatrixOrder`.

### Local helper

Prove locally:

```lean
one_le_det_one_add_psd
    (hC : C.PosSemidef) : 1 ≤ (1 + C).det
```

Route:

1. Rewrite `C` using `hC.isHermitian.spectral_theorem`.
2. Move `1` through the unitary conjugation using `map_one`, `map_add`.
3. Show determinant invariance under that conjugation using:

   - `Unitary.conjStarAlgAut_apply`
   - `Matrix.det_mul`
   - `Unitary.coe_star`
   - `Unitary.coe_mul_star_self`
   - `Matrix.det_one`

4. Reduce the result to

   ```lean
   ∏ i, (1 + hC.isHermitian.eigenvalues i)
   ```

   using:

   - `Matrix.diagonal_one`
   - `Matrix.diagonal_add`
   - `Matrix.det_diagonal`

5. Finish with `Finset.one_le_prod` and `hC.eigenvalues_nonneg i`.

This helper skeleton was Lean-checked at the pin.

### Main skeleton

Let `D := B - A` and first obtain:

```lean
have hB : B.PosSemidef := by
  simpa only [sub_add_cancel] using hD.add hA
```

Split on `hApd : A.PosDef`.

In the positive-definite case:

```lean
let S := CFC.sqrt A
have hSunit : IsUnit S :=
  (CFC.isUnit_sqrt_iff A hA.nonneg).mpr hApd.isUnit
letI := hSunit.invertible

have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
let C := S⁻¹ * D * S⁻¹
```

Prove `hC : C.PosSemidef` from:

- `hD.mul_mul_conjTranspose_same S⁻¹`
- `hSpsd.isHermitian.inv`
- `Matrix.IsHermitian.eq`

Then establish

```lean
B = S * (1 + C) * S
```

using `CFC.sqrt_mul_sqrt_self`, `Matrix.inv_mul_of_invertible`, associativity, and ring normalization.

Finally use:

- `one_le_det_one_add_psd hC`
- `hSpsd.det_nonneg`
- `Matrix.det_mul`

to compare
`det A = det S · det S`
with
`det B = det S · det (1+C) · det S`.

In the non-positive-definite case, derive `A.det = 0` using:

- `hA.posDef_iff_isUnit`
- `Matrix.isUnit_iff_isUnit_det`
- `isUnit_iff_ne_zero`

and finish from `hB.det_nonneg`.

## Q2

### (a) Avoiding shrinking images

A uniform fixed-\(A\) bound is false. Taking  
\(A=\varepsilon[I_m\;0]\) makes the inner integral scale like \(\varepsilon^{-ab}\).

There is a clean paper route via Gaussians:

1. Dominate the box integral by the corresponding full-space Gaussian integral; Gaussian density is bounded below on the unit box.
2. For independent standard Gaussian matrices \(Y\) and \(A\), condition on \(Y\). If
   \(S=(YY^\top)^{1/2}\), then

   \[
   YA\ \stackrel{d}{=}\ SZ,
   \]

   with \(Z\) a standard Gaussian \(b\times q\) matrix.
3. Hence

   \[
   \det((YA)(YA)^\top)
   =\det(YY^\top)\det(ZZ^\top),
   \]

   and the moment factors into the \(b\times m\) and \(b\times q\) single-matrix moments.
4. These are finite for \(a<m-b+1\) and \(a<q-b+1\).

This bypasses column-drop and Q1 entirely.

However, it is not turnkey in Mathlib v4.29. Confirmed primitives include:

- `ProbabilityTheory.stdGaussian`
- `ProbabilityTheory.multivariateGaussian`
- `ProbabilityTheory.IsGaussian.ext`
- `ProbabilityTheory.charFun_multivariateGaussian`
- `MeasureTheory.lintegral_prod`
- `Matrix.PosSemidef.det_sqrt`

But there is no Wishart distribution or negative determinant-moment theorem, nor a ready matrix-product Gaussian factorization lemma. Those must be built.

### (b) Verdict

**STOP-and-report-to-controller for the present tide.**

The linear Jacobian itself is standard and already banked. The missing part is the analytic estimate over the variable shrinking image.

Indeed,

\[
\int_{\mathrm{box}}F(YT)\,dY
=|\det T|^{-b}\int_{\mathrm{box}\cdot T}F(X)\,dX.
\]

The image volume cancels the Jacobian only for a bounded integrand. Here \(F\) is singular. In the scalar case,

\[
|t|^{-1}\int_{-|t|}^{|t|}|x|^{-a}\,dx
\asymp |t|^{-a},
\]

so nontrivial \(t\)-dependence remains. In higher dimensions it depends anisotropically on all singular values of \(T\). The banked fixed-box lemma supplies no such quantitative estimate.

Thus this is not merely image-domain bookkeeping; a new analytic lemma is required.

### (c) Recommended reduction and exact CoV API

I recommend banking the Gaussian product-moment factorization as a separate reusable result. That is the cleanest closure route, though it is a substantial new measure/probability module.

If pursuing the original restricted-image route, use the raw Pi-space operator already present in the repo:

- `DLNFibre.DLN.RLCT.rightMulₚ`
- `DLNFibre.DLN.RLCT.det_rightMulₚ`
- `DLNFibre.DLN.RLCT.lintegral_comp_rightMulₚ`

The underlying confirmed Mathlib API is:

- `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`
- `MeasureTheory.lintegral_map`
- `MeasureTheory.lintegral_smul_measure`
- `LinearMap.det_pi`
- `LinearMap.det_toLin'`
- `Matrix.det_transpose`
- `LinearMap.continuous_of_finiteDimensional`

There is no ready named theorem for the required restricted-image formula. It must be derived using an indicator of `rightMulₚ b T '' matBox ...`, followed by a new estimate of its singular integral. That final estimate—not the CoV API—is the blocker.