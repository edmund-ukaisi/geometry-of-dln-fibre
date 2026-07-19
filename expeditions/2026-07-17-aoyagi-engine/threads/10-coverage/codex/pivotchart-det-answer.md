The cleanest route is neither block reindexing nor an invertible-case split. Convert the derivative to its standard matrix, then use one row-operation invariance lemma:

\[
A_{k\ell}=B_{k\ell}+c_kB_{i\ell},
\]

where \(B=\operatorname{diag}(b)\), \(b_i=1\), \(b_k=u_i\) for \(k\ne i\), and \(c_i=0,\ c_k=u_k\).

The exact v4.29 lemma is:

```lean
Matrix.det_eq_of_forall_row_eq_smul_add_const
```

It states precisely that adding multiples of row `B i` to all other rows preserves the determinant.

### Skeleton

```lean
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped BigOperators

noncomputable def pivotChartDeriv {d : ℕ} (i : Fin d) (u : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun k ↦
    if k = i then
      ContinuousLinearMap.proj i
    else
      u i • ContinuousLinearMap.proj k +
        u k • ContinuousLinearMap.proj i

theorem pivotChart_hasFDerivAt {d : ℕ} (i : Fin d) (u : Fin d → ℝ) :
    HasFDerivAt (pivotChart i) (pivotChartDeriv i u) u := by
  apply hasFDerivAt_pi''
  intro k
  rw [pivotChartDeriv, ContinuousLinearMap.proj_pi]
  rcases eq_or_ne k i with rfl | hk
  · have hcomp :
        (fun y : Fin d → ℝ ↦ pivotChart i y i) = fun y ↦ y i := by
      funext y
      simp [pivotChart]
    rw [if_pos rfl, hcomp]
    exact hasFDerivAt_apply i u
  · have hcomp :
        (fun y : Fin d → ℝ ↦ pivotChart i y k) = fun y ↦ y i * y k := by
      funext y
      simp [pivotChart, hk]
    rw [if_neg hk, hcomp]
    exact (hasFDerivAt_apply i u).mul (hasFDerivAt_apply k u)
```

The standard-matrix entry formula uses `LinearMap.toMatrix'_apply`:

```lean
private theorem pivotChartDeriv_toMatrix {d : ℕ}
    (i : Fin d) (u : Fin d → ℝ) (k l : Fin d) :
    LinearMap.toMatrix'
        (pivotChartDeriv i u :
          (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) k l =
      if k = i then
        if l = i then 1 else 0
      else
        u i * (if l = k then 1 else 0) +
          u k * (if l = i then 1 else 0) := by
  rw [LinearMap.toMatrix'_apply]
  change (pivotChartDeriv i u) (Pi.single l 1) k = _
  rw [pivotChartDeriv]
  simp only [ContinuousLinearMap.pi_apply]
  rcases eq_or_ne k i with rfl | hk
  · by_cases hl : l = i <;> simp [hl, eq_comm]
  · simp only [if_neg hk, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_apply, smul_eq_mul]
    by_cases hl₁ : l = k <;> by_cases hl₂ : l = i <;>
      simp_all [eq_comm]
```

Then the determinant:

```lean
theorem pivotChartDeriv_det {d : ℕ} (i : Fin d) (u : Fin d → ℝ) :
    (pivotChartDeriv i u).det = u i ^ (d - 1) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']

  set A := LinearMap.toMatrix'
    (pivotChartDeriv i u :
      (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) with hA

  let b : Fin d → ℝ := fun k ↦ if k = i then 1 else u i
  let c : Fin d → ℝ := fun k ↦ if k = i then 0 else u k

  have hdet : A.det = (Matrix.diagonal b).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const c i
    · simp [c]
    · intro k l
      rw [hA, pivotChartDeriv_toMatrix]
      by_cases hk : k = i
      · subst k
        by_cases hl : l = i <;>
          simp [b, c, Matrix.diagonal_apply, hl, eq_comm]
      · by_cases hl₁ : l = k <;> by_cases hl₂ : l = i <;>
          simp_all [b, c, Matrix.diagonal_apply, eq_comm]

  rw [hdet, Matrix.det_diagonal]
  calc
    (∏ k : Fin d, b k) =
        ∏ k in (Finset.univ : Finset (Fin d)).erase i, b k :=
      (Finset.prod_erase (f := b) (a := i) Finset.univ
        (by simp [b])).symm
    _ = u i ^ ((Finset.univ : Finset (Fin d)).erase i).card := by
      apply Finset.prod_eq_pow_card
      intro k hk
      simp [b, Finset.ne_of_mem_erase hk]
    _ = u i ^ (d - 1) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]

theorem pivotChart_fderiv_det {d : ℕ} (i : Fin d) (u : Fin d → ℝ) :
    (fderiv ℝ (pivotChart i) u).det = u i ^ (d - 1) := by
  rw [(pivotChart_hasFDerivAt i u).fderiv]
  exact pivotChartDeriv_det i u

theorem pivotChart_abs_fderiv_det {d : ℕ} (i : Fin d) (u : Fin d → ℝ) :
    |(fderiv ℝ (pivotChart i) u).det| = |u i| ^ (d - 1) := by
  rw [pivotChart_fderiv_det, abs_pow]
```

No separate `d ≥ 1` hypothesis is needed: the argument `i : Fin d` already makes the `d = 0` case uninhabited.

### Exact v4.29 names

Source-checked at the pinned checkout:

- `hasFDerivAt_pi`, `hasFDerivAt_pi''`
- `hasFDerivAt_apply`
- `HasFDerivAt.mul`
- `ContinuousLinearMap.proj_pi`
- `LinearMap.toMatrix'`
- `LinearMap.toMatrix'_apply`
- `LinearMap.det_toMatrix'`
- `LinearMap.det_toMatrix`
- `Matrix.det_eq_of_forall_row_eq_smul_add_const`
- `Matrix.det_diagonal`
- `Matrix.det_fromBlocks_zero₁₂`
- `Matrix.det_fromBlocks_zero₂₁`
- `Matrix.det_reindex_self`
- `Matrix.det_reindex`
- `Matrix.abs_det_reindex`
- `Matrix.det_smul` — argument order is `Matrix.det_smul A c`
- `Matrix.det_one`

There is no `Matrix.det_reindexₐ` at this pin. For absolute values under independently reindexed rows and columns, the exact lemma is `Matrix.abs_det_reindex`.

`ContinuousLinearMap.det` is only an abbreviation for the underlying `LinearMap.det`; the standard bridge idiom is exactly:

```lean
rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
```

Using raw `Fin d → ℝ` and `toMatrix'` avoids basis and module-instance diamonds. If using the general bridge, the basis is `Pi.basisFun ℝ (Fin d)` and its type is `Module.Basis ...`, not bare `Basis`.

Finally, the shear factorization is valid:

```text
D = transvection (proj i) v ∘ diagonalScaling b
```

with `v i = 0` and `v k = u k` otherwise. The exact determinant theorem is `LinearMap.transvection.det`, in `Mathlib.LinearAlgebra.Transvection.Basic`, together with `LinearMap.det_comp` and `LinearMap.det_pi`. It is conceptually elegant, but the row lemma above encodes the same shear in substantially less Lean.