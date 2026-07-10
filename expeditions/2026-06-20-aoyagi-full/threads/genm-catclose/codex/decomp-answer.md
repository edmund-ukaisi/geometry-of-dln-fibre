**1. ROUTE VERDICT**

Use the row-residual Schur recursion. It is still the cheapest sorry-free route, but prove P3 through an explicit least-squares residual, not a projection matrix `M`. Gram-Schmidt is not cheaper: the useful determinant API is square/ambient-dimension oriented and still leaves singular/rank bookkeeping. SVD/global orthogonal CoV is worse: no cheap packaged SVD, and measurable frame selection is exactly the wrong Lean problem.

Also split `a = 0` first; then the integral is just volume of the box. The recursive “det = 0 gives integrand 0” branch needs `-a/2 ≠ 0`.

**2. P3**

Pick **(c), with Submodule only at the end**.

For rows `u : ι → E`, `E := EuclideanSpace ℝ (Fin q)`, set

```lean
G : Matrix ι ι ℝ := Matrix.gram ℝ u
y : ι → ℝ := fun i => ⟪u i, w⟫_ℝ
c : ι → ℝ := ⅟G *ᵥ y
p : E := ∑ i, c i • u i
r : E := w - p
V : Submodule ℝ E := Submodule.span ℝ (Set.range u)
```

Under `hG : G.det ≠ 0`:

```lean
letI : Invertible G :=
  Matrix.invertibleOfIsUnitDet G (isUnit_iff_ne_zero.mpr hG)
```

Core local lemmas to build:

```lean
G *ᵥ c = y
r ∈ Vᗮ
schurScalar G y w = ‖r‖ ^ 2
r = Vᗮ.starProjection w
```

Use these Mathlib facts:

- `Matrix.det_fromBlocks₁₁`
- `Matrix.det_fin_one`
- `Matrix.det_reindex_self` / `Matrix.det_submatrix_equiv_self`
- `Matrix.mulVec_mulVec`
- `Matrix.mul_invOf_self`, `Matrix.invOf_mul_self`
- `Matrix.star_dotProduct_gram_mulVec`
- `Submodule.mem_orthogonal'`
- `Submodule.span_induction`
- `Submodule.eq_starProjection_of_mem_orthogonal'`
- `Submodule.starProjection_orthogonal_val`
- `real_inner_self_eq_norm_sq`

Avoid the matrix projection `M = I - QᵀG⁻¹Q`; proving `M² = M`, symmetry, range/kernel, and quadratic-form equality is more work than the residual normal-equation proof.

**3. P2**

Do **not** use the lower bound to a smaller projection with `Real.rpow` + `ENNReal.ofReal`. Pointwise monotonicity fails at zeros: for `a > 0`, `0 ^ (-a) = 0` in `Real.rpow`, so `‖P_U w‖ ≥ ‖P_W w‖` does not imply the desired `ofReal` inequality when `P_W w = 0`.

Clean route: prove the bound for the **actual projection** `U.starProjection`, then make the constant uniform by finite maximization over possible ranks.

Interface:

```lean
theorem projection_rpow_lintegral_uniform
    (q r : ℕ) (hr : 1 ≤ r) (hrq : r ≤ q)
    {a : ℝ} (ha : a < r) (R : ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ U : Submodule ℝ (EuclideanSpace ℝ (Fin q)),
        r ≤ Module.finrank ℝ U →
        (∫⁻ w in Metric.ball 0 R,
          ENNReal.ofReal (‖U.starProjection w‖ ^ (-a))) ≤ C
```

For fixed `U`, use:

- `Submodule.orthogonalDecomposition`
- `Submodule.fst_orthogonalDecomposition_apply`
- `Submodule.snd_orthogonalDecomposition_apply`
- `LinearIsometryEquiv.measurePreserving`
- `LinearIsometryEquiv.toMeasurableEquiv`
- `WithLp.volume_preserving_ofLp` / `WithLp.volume_preserving_toLp`
- `OrthonormalBasis.measurePreserving_repr` / `measurePreserving_repr_symm`
- `MeasurePreserving.setLIntegral_comp_emb`
- `MeasureTheory.setLIntegral_prod`
- `Bornology.IsBounded.measure_lt_top` or `measure_ball_ne_top`

Uniformity: define `radC` as a finite sum over `d ∈ Finset.Icc r q` of the Euclidean radial integrals, and `kerC` as a finite sum over `k ∈ Finset.range (q+1)` of kernel-ball volumes. Then `C := radC * kerC`.

No measurable family of orthogonal changes of variables is needed; each `U` is handled pointwise.

**4. RISK RANKING**

1. **P3 highest risk**: normal-equation algebra plus block/reindex bookkeeping.
2. **P2 medium risk**: product decomposition and finite-rank-uniform constant.
3. **P4 lower risk**: Tonelli and row splitting are routine once P2/P3 exist.

Fallback for P3: state and prove the Schur brick over `Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) ℝ` first. Only later wrap the `Fin b` row split with `Matrix.det_reindex_self`. This avoids fighting `Fin.last`/`Fin.cast` while proving the algebra.

**5. SCOPE CALL**

Separate P2 and P3. This is not one comfortable tide unless the projection bound is already built.

Minimal clean interfaces:

```lean
-- P3
det_gram_appendRow_eq :
  G.det ≠ 0 →
  det (Matrix.gram ℝ (Sum.elim u (fun _ : Fin 1 => w)))
    = G.det * ‖(Submodule.span ℝ (Set.range u))ᗮ.starProjection w‖ ^ 2

det_gram_appendRow_eq_zero_of_det_zero :
  G.det = 0 →
  det (Matrix.gram ℝ (Sum.elim u (fun _ : Fin 1 => w))) = 0
```

```lean
-- P2
projection_rpow_lintegral_uniform :
  ∃ C < ⊤, ∀ U, r ≤ finrank ℝ U →
    ∫⁻ w in ball 0 R, ofReal (‖U.starProjection w‖ ^ (-a)) ≤ C
```

Then P4 is just Schur + `Real.mul_rpow` + `ENNReal.ofReal_mul` + Tonelli + induction.