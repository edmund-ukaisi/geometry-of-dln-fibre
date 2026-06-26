**1. Route Choice**

Choose **(a)**. Do the determinant abstractly after splitting matrix entries into `lower × diagonal × upper` coordinates and stripping the fixed unitriangular `L,U` factors. Route **(b)** is possible, but opaque-`t` `BlockTriangular` over `t^2` entries will be a bespoke global-order/index-arithmetic proof. The abstract route still has index work, but only for off-diagonal fiber counts.

**2. Lemma Chain / Definition Shape**

Use parameter coordinates:

```lean
abbrev LowIdx t := {p : Fin t × Fin t // p.2 < p.1}
abbrev UpIdx  t := {p : Fin t × Fin t // p.1 < p.2}

abbrev LDUParam t :=
  (LowIdx t → ℝ) × ((Fin t → ℝ) × (UpIdx t → ℝ))
```

Define:

```lean
lowMat  : (LowIdx t → ℝ) →ₗ[ℝ] Matrix (Fin t) (Fin t) ℝ
upMat   : (UpIdx t → ℝ) →ₗ[ℝ] Matrix (Fin t) (Fin t) ℝ
unitLow l := 1 + lowMat l
unitUp  u := 1 + upMat u
```

and a linear equivalence:

```lean
matrixSplit : Matrix (Fin t) (Fin t) ℝ ≃ₗ[ℝ] LDUParam t
```

reading strict-lower, diagonal, strict-upper entries.

Define the raw Frechet derivative to matrices:

```lean
lduCoreDerivMatrix l q u : LDUParam t →ₗ[ℝ] Matrix (Fin t) (Fin t) ℝ
| dl, dq, du ↦
    lowMat dl * Matrix.diagonal q * unitUp u
  + unitLow l * Matrix.diagonal dq * unitUp u
  + unitLow l * Matrix.diagonal q * upMat du
```

Then define the determinant-facing endomorphism:

```lean
lduCoreDeriv l q u :=
  matrixSplit.toLinearMap.comp (lduCoreDerivMatrix l q u)
```

Proof chain:

Use existing/local confirmed lemmas:
`LinearMap.det_comp`, `LinearMap.det_id`, `LinearMap.det_conj`,
`LinearMap.det_pi`, `LinearMap.det_eq_det_mul_det`,
`Matrix.det_of_lowerTriangular`, `Matrix.det_transpose`,
`Matrix.det_mul`, `Matrix.det_diagonal`,
your `lowerTri_det`, `det_mulLeft_matrixSpace`, `det_mulRight_matrixSpace`.

Build local lemmas:
`det_unitLower = 1`, `det_unitUpper = 1`;
det-one action of unitriangular left/right multiplication on strict lower/upper coordinate spaces;
`det_scale_lower q = ∏ i, q i ^ (t - 1 - i)`;
`det_scale_upper q = ∏ i, q i ^ (t - 1 - i)`.

Then assemble:

```lean
det lduCoreDeriv
= det(det-one unit changes)
  * det(scaleLower q)
  * det(id diagonal)
  * det(scaleUpper q)
= ∏ i, q i ^ (2 * (t - 1 - i))
```

and finish absolute values with `abs_mul`, `abs_pow`.

**3. Existing Mathlib Lemma?**

No ready-made Mathlib lemma for the LDU/Bruhat parametrization Jacobian. Build it.

For full matrix-space scaling, use your landed A1 lemmas. For strict-lower/strict-upper restricted scaling, build local lemmas via `LinearMap.det_pi` and product counting. I would not rely on `Matrix.transvection` here; relevant names/details are **VERIFY**, and they will not package this Jacobian anyway.

**4. Size Assessment**

Not Size S. I would rate A3 as **medium**: the algebraic idea is small, but the durable Lean cost is the coordinate split equivalence plus determinant-one unitriangular restriction lemmas and the product-count rewrite over `LowIdx`/`UpIdx`. Biggest risk: proving the strict triangular unit-action determinants without drifting into the same opaque-`t` matrix-index proof route you were trying to avoid.