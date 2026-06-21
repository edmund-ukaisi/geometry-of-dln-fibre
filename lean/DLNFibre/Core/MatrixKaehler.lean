import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# `DLNFibre.Core.MatrixKaehler` — entrywise matrix calculus + a base-change rank brick

A bounded slice of matrix differential calculus over a `Derivation R A M` (`A` a commutative ring,
`M` an `A`-module), enough to differentiate `genericUnit · genericUnitInv = 1` for the A4.3
differential-rank bound. Mathlib v4.29 has no matrix-`Derivation` API, and `Matrix.mul` requires a
single element type with `Mul`, so a `Matrix _ _ M` (entries in the module `M`) cannot be multiplied
by a `Matrix _ _ A` directly. We therefore phrase everything **entrywise** (scalar `M`-equations
with explicit `Finset.sum`), using the `A`-module structure `•` for the mixed `A`/`M` products.

The two derivation facts, for `D : Derivation R A M`:

* **Entrywise matrix-product Leibniz** (`derivMatrix_mul_apply`): for `A`-matrices `P, Q`,
  `D ((P * Q) r c) = Σ_s ( P r s • D (Q s c) + Q s c • D (P r s) )`.
* **The matrix-Kähler inverse identity** (`derivMatrix_inv_apply`): if `U * U⁻¹ = 1` entrywise over
  `A`, then `D ((U⁻¹) r c) = − Σ_{s,t} (U⁻¹ r s) • (U⁻¹ t c) • D (U s t)` — the entrywise
  `D(U⁻¹) = −U⁻¹ (DU) U⁻¹`.

Plus a base-change rank brick (`finrank_range_baseChange`): for a `k`-linear `f` between `k`-spaces
and a field extension `K/k`, `finrank K (range (f.baseChange K)) = finrank k (range f)` — base
change preserves the rank of a linear map. This is the rank-side tool the A4.3 generic-Jacobian
bound consumes (`genericDifferentialRank` over `K = FractionRing B` vs `finrank` over `k`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix Finset

variable {R A M : Type*} [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M] [IsScalarTower R A M] (D : Derivation R A M)

omit [IsScalarTower R A M] in
/-- **Entrywise matrix-product Leibniz.** Differentiating the `(r,c)` entry of a matrix product
`P * Q` (over the commutative ring `A`) through `D : Derivation R A M`:
`D ((P * Q) r c) = Σ_s ( P r s • D (Q s c) + Q s c • D (P r s) )`. The `(P · DQ + Q · DP)`-rule,
entrywise; `Matrix.mul_apply` + `map_sum` (`D` additive) + per-term `Derivation.leibniz`. -/
theorem derivMatrix_mul_apply {l m n : Type*} [Fintype m] (P : Matrix l m A) (Q : Matrix m n A)
    (r : l) (c : n) :
    D ((P * Q) r c) = ∑ s : m, (P r s • D (Q s c) + Q s c • D (P r s)) := by
  rw [Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [D.leibniz]

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [IsScalarTower R A M] in
/-- For each fixed source column `c`, `Σ_s U r s • D (W s c) = − Σ_s W s c • D (U r s)` — the
entrywise `(DU)·W + U·(DW) = 0` read off `D ((U*W) r c) = D 1 = 0`. -/
theorem derivMatrix_inv_aux {U W : Matrix m m A} (hUW : U * W = 1) (r c : m) :
    ∑ s : m, U r s • D (W s c) = - ∑ s : m, W s c • D (U r s) := by
  classical
  have hzero : (0 : M) = ∑ s : m, (U r s • D (W s c) + W s c • D (U r s)) := by
    rw [← derivMatrix_mul_apply D U W r c, hUW, Matrix.one_apply]
    by_cases h : r = c
    · subst h; simp
    · simp [h]
  rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]; exact hzero.symm

omit [IsScalarTower R A M] in
/-- **The matrix-Kähler inverse identity (entrywise).** For square `A`-matrices `U, W` with
`U * W = 1`, the derivation of `W`'s `(r,c)` entry is
`D (W r c) = − Σ_{s,t} (W r s) • (W t c) • D (U s t)` — the entrywise `D(U⁻¹) = −U⁻¹ (DU) U⁻¹`,
proved from `D(U·W) = D 1 = 0` via the product Leibniz, then left-multiplying by `W` and using
`W * U = 1` to invert `U` on the left of `D W`. Models `W = U⁻¹`. -/
theorem derivMatrix_inv_apply {U W : Matrix m m A} (hUW : U * W = 1) (r c : m) :
    D (W r c) = - ∑ s : m, ∑ t : m, (W r s) • (W t c) • D (U s t) := by
  classical
  have hWU : W * U = 1 := mul_eq_one_comm.mp hUW
  -- `Σ_p W r p • Σ_s U p s • D(W s c) = Σ_s (Σ_p W r p * U p s) • D(W s c) = D (W r c)` (since
  -- `Σ_p W r p U p s = (W*U) r s = δ_{rs}`)
  have hstart : ∑ p : m, W r p • ∑ s : m, U p s • D (W s c) = D (W r c) := by
    have e1 : ∀ p : m, W r p • ∑ s : m, U p s • D (W s c)
        = ∑ s : m, (W r p * U p s) • D (W s c) := fun p ↦ by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun s _ ↦ by rw [smul_smul]
    rw [Finset.sum_congr rfl fun p _ ↦ e1 p, Finset.sum_comm]
    have e2 : ∀ s : m, ∑ p : m, (W r p * U p s) • D (W s c)
        = (W * U) r s • D (W s c) := fun s ↦ by
      rw [← Finset.sum_smul, Matrix.mul_apply]
    rw [Finset.sum_congr rfl fun s _ ↦ e2 s, hWU]
    rw [Finset.sum_eq_single r]
    · rw [Matrix.one_apply_eq, one_smul]
    · exact fun b _ hb ↦ by rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
    · exact fun h ↦ absurd (Finset.mem_univ r) h
  -- substitute the auxiliary identity and match termwise
  rw [← hstart]
  have e3 : ∀ p : m, W r p • ∑ s : m, U p s • D (W s c)
      = - ∑ s : m, W r p • W s c • D (U p s) := fun p ↦ by
    rw [derivMatrix_inv_aux D hUW p c, smul_neg, Finset.smul_sum]
  rw [Finset.sum_congr rfl fun p _ ↦ e3 p, Finset.sum_neg_distrib]

/-! ## Base-change rank brick -/

open Module LinearMap in
/-- **Base change preserves the rank of a linear map.** For `f : V →ₗ[k] W` between `k`-modules with
`range f` finite-dimensional, and a field extension `K/k`, the base-changed map `f.baseChange K`
(`= K ⊗ f`) has `finrank K (range (f.baseChange K)) = finrank k (range f)`. Factor
`f = subtype ∘ rangeRestrict`; base change preserves the surjection (`lTensor_surjective`, so the
range of the base-changed `rangeRestrict` is `⊤`) and the injection (over the flat `K`, via
`Flat.lTensor_preserves_injective_linearMap`, so the range of the base-changed `subtype` is
`≅ K ⊗ range f`); then `Module.finrank_baseChange`. The rank-side tool for the A4.3 bound. -/
theorem finrank_range_baseChange {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (K : Type*) [Field K] [Algebra k K]
    (f : V →ₗ[k] W) [Module.Finite k (LinearMap.range f)] :
    finrank K (LinearMap.range (f.baseChange K)) = finrank k (LinearMap.range f) := by
  have hfac : f.baseChange K
      = (LinearMap.range f).subtype.baseChange K ∘ₗ f.rangeRestrict.baseChange K := by
    rw [← LinearMap.baseChange_comp, subtype_comp_codRestrict]
  rw [hfac, LinearMap.range_comp]
  have hsurj : LinearMap.range (f.rangeRestrict.baseChange K) = ⊤ := by
    rw [LinearMap.range_eq_top, LinearMap.baseChange_eq_ltensor]
    exact lTensor_surjective K f.surjective_rangeRestrict
  rw [hsurj, Submodule.map_top]
  have hinj : Function.Injective ((LinearMap.range f).subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

end DLNFibre.Core
