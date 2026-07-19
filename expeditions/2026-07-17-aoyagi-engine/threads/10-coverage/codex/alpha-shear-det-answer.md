The cleanest route is to recognize the derivative as `LinearMap.transvection`. Mathlib already proves its determinant formula, so no matrix or nilpotence argument is needed.

```lean
import Mathlib

abbrev V (d : ℕ) := Fin d → ℝ

def shear {d : ℕ} (a b c : Fin d) (x : V d) : V d :=
  Function.update x a (x a - x b * x c)

def unshear {d : ℕ} (a b c : Fin d) (x : V d) : V d :=
  Function.update x a (x a + x b * x c)
```

### 1. Homeomorphism

`Homeomorph.mk` takes an `Equiv`, followed by continuity of its forward and inverse maps.

```lean
def shearHomeomorph {d : ℕ} (a b c : Fin d)
    (hab : a ≠ b) (hac : a ≠ c) : V d ≃ₜ V d :=
  Homeomorph.mk
    { toFun := shear a b c
      invFun := unshear a b c
      left_inv := by
        intro x
        ext i
        by_cases hi : i = a
        · subst i
          simp [shear, unshear, hab, hab.symm, hac, hac.symm]
        · simp [shear, unshear, hi]
      right_inv := by
        intro x
        ext i
        by_cases hi : i = a
        · subst i
          simp [shear, unshear, hab, hab.symm, hac, hac.symm]
        · simp [shear, unshear, hi] }
    (by
      simpa [shear] using
        continuous_id.update a
          ((continuous_apply a).sub
            ((continuous_apply b).mul (continuous_apply c))))
    (by
      simpa [unshear] using
        continuous_id.update a
          ((continuous_apply a).add
            ((continuous_apply b).mul (continuous_apply c))))
```

At v4.29, `by fun_prop` or `by continuity` should also close both continuity fields: `continuous_update` carries both `[fun_prop]` and `[continuity]`. The explicit route above uses:

- `Continuous.update`
- `continuous_apply`
- `Continuous.mul`, `.add`, `.sub`

No hypothesis `b ≠ c` is needed.

### 2. Explicit derivative

Use `ContinuousLinearMap.proj` for coordinate covectors and `Pi.single a 1` for the basis vector.

```lean
def wCLM {d : ℕ} (b c : Fin d) (x : V d) : V d →L[ℝ] ℝ :=
  -(x b • (ContinuousLinearMap.proj c : V d →L[ℝ] ℝ) +
    x c • (ContinuousLinearMap.proj b : V d →L[ℝ] ℝ))

def shearDeriv {d : ℕ} (a b c : Fin d) (x : V d) : V d →L[ℝ] V d :=
  ContinuousLinearMap.id ℝ (V d) +
    (wCLM b c x).smulRight (Pi.single a 1)
```

Thus

```lean
wCLM b c x h = -(x c) * h b - (x b) * h c
```

up to elementary ring normalization.

The useful rewrite is

```lean
lemma shear_eq_add_single {d : ℕ} (a b c : Fin d) :
    shear a b c =
      fun x => x + (-(x b * x c)) • (Pi.single a 1 : V d) := by
  -- funext x i; by_cases i = a; simp [shear, Function.update_apply, Pi.single_apply, *]
  ...
```

Then the derivative uses exactly:

- `hasFDerivAt_id`
- `hasFDerivAt_apply`
- `HasFDerivAt.mul`
- `HasFDerivAt.neg`
- `HasFDerivAt.smul_const`
- `HasFDerivAt.add`

```lean
lemma shear_hasFDerivAt {d : ℕ} (a b c : Fin d) (x : V d) :
    HasFDerivAt (shear a b c) (shearDeriv a b c x) x := by
  rw [shear_eq_add_single (a := a) (b := b) (c := c)]
  have hp :=
    (hasFDerivAt_apply (𝕜 := ℝ) b x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) c x)
  have hn := hp.neg
  simpa [shearDeriv, wCLM] using
    (hasFDerivAt_id (𝕜 := ℝ) x).add
      (hn.smul_const (Pi.single a 1 : V d))
```

Pitfall: `hasFDerivAt_update x y` exists, but differentiates the scalar-variable map

```lean
fun y => Function.update x i y
```

with fixed `x`. It is not a `HasFDerivAt.update` combinator for a varying Pi-valued base. Componentwise alternatives are `hasFDerivAt_pi`, `hasFDerivAt_pi'`, and `hasFDerivAt_apply`, but the `Pi.single` rewrite is shorter here.

### 3. Determinant

The key exact lemma is:

```lean
LinearMap.transvection.det
```

Its content is

```lean
(LinearMap.transvection f v).det = 1 + f v
```

for a finite free module, and

```lean
LinearMap.transvection f v h = h + f h • v
```

by `LinearMap.transvection.apply`.

```lean
lemma shearDeriv_det {d : ℕ} (a b c : Fin d)
    (hab : a ≠ b) (hac : a ≠ c) (x : V d) :
    (shearDeriv a b c x).det = 1 := by
  change LinearMap.det (shearDeriv a b c x).toLinearMap = 1

  have htr :
      (shearDeriv a b c x).toLinearMap =
        LinearMap.transvection (wCLM b c x).toLinearMap
          (Pi.single a 1 : V d) := by
    ext h
    rfl

  have hwa : wCLM b c x (Pi.single a 1 : V d) = 0 := by
    simp [wCLM, Pi.single_apply, hab, hac]

  rw [htr, LinearMap.transvection.det]
  change 1 + wCLM b c x (Pi.single a 1 : V d) = 1
  simp [hwa]
```

Hence:

```lean
lemma abs_det_fderiv_shear {d : ℕ} (a b c : Fin d)
    (hab : a ≠ b) (hac : a ≠ c) (x : V d) :
    |(fderiv ℝ (shear a b c) x).det| = 1 := by
  rw [(shear_hasFDerivAt a b c x).fderiv,
      shearDeriv_det a b c hab hac x]
  exact abs_one
```

### Matrix alternatives

They are unnecessary, but the exact v4.29 names are:

- No convenient general `det (1 + N) = 1` nilpotence lemma was found.
- `Matrix.det_one_add_col_mul_row` does not exist.
- The rank-one lemma is:

```lean
Matrix.det_one_add_replicateCol_mul_replicateRow
```

with conclusion

```lean
det (1 + replicateCol ι u * replicateRow ι v) = 1 + v ⬝ᵥ u
```

where `[Unique ι]`; normally take `ι := Unit`. Related: `Matrix.vecMulVec_eq Unit`.

- The row-operation lemma is:

```lean
Matrix.det_updateRow_add_smul_self
```

not `Matrix.det_updateRow_add_smul`.

For conversion, use `LinearMap.det_toMatrix` with `Pi.basisFun ℝ (Fin d)`, or more directly `LinearMap.det_toMatrix'`.

### Instances and measure theory

`ContinuousLinearMap.det` is a noncomputable abbreviation for the determinant of `.toLinearMap`. On `Fin d → ℝ`, the required `Module.Free`, `Module.Finite`/`FiniteDimensional`, `Fintype`, and `DecidableEq` instances are inferred automatically.

There is no measure-preserving shortcut to the pointwise determinant claim. One could prove volume preservation after splitting off coordinate `a`, using `MeasurePreserving.skew_product` and translation invariance, but that is longer and does not itself imply the desired pointwise `fderiv` determinant equality.