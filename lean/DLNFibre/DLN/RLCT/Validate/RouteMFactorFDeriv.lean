import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Matrix.Mul

/-!
# `RouteMFactorFDeriv` — the matrix-valued fderiv plumbing for the achiever-chart factor maps

The nonlinear achiever-chart factors (the Schur frame `S(X,K,N,E) = [[K,KN],[XK, XKN+E]]`, the LDU
core `L·diag q·U`) are products and sums of matrix blocks. To package them as `ChartFactor`s (via
`RouteMConjBlock.conjBlockFactor`) the nonlinear maps need `HasFDerivAt` on their `Matrix`-typed
block space. `Matrix` carries no `NormedAddCommGroup` instance by default (Mathlib avoids the
topology diamond), so this module installs the **pi-norm** structure on `Matrix (Fin l) (Fin m) ℝ`
(via `inferInstanceAs` on the unfolded `Fin l → Fin m → ℝ` — the norm topology is `rfl`-equal to the
canonical matrix product topology, no diamond) and the matrix-mult **bounded bilinear CLM**
`matMulBilin`, then the product/sum fderiv corollaries.

* `instNormedAddCommGroupMatrix` / `instNormedSpaceMatrix` / `instFiniteDimensionalMatrix` — the
  diamond-free normed structure on a finite real matrix space.
* `matMulBilin` / `matMulBilin_apply` — matrix multiplication as a continuous bilinear map.
* `HasFDerivAt.matMul` — the product rule `D(f·g) = (f x)·g' + f'·(g x)` for matrix-valued maps.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus; no S2).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-! ## The diamond-free pi-norm structure on a finite real matrix space -/

/-- `Matrix (Fin l) (Fin m) ℝ` inherits the **pi-norm** `NormedAddCommGroup` (the sup/product norm on
the unfolded `Fin l → Fin m → ℝ`). Its induced topology is `rfl`-equal to the canonical matrix
product topology (`instTopologicalSpaceMatrix`) — no diamond. -/
noncomputable instance instNormedAddCommGroupMatrix (l m : ℕ) :
    NormedAddCommGroup (Matrix (Fin l) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin l → Fin m → ℝ))

/-- `Matrix (Fin l) (Fin m) ℝ` inherits the pi-norm `NormedSpace ℝ`. -/
noncomputable instance instNormedSpaceMatrix (l m : ℕ) :
    NormedSpace ℝ (Matrix (Fin l) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin l → Fin m → ℝ))

/-- `Matrix (Fin l) (Fin m) ℝ` is finite-dimensional over `ℝ`. -/
instance instFiniteDimensionalMatrix (l m : ℕ) :
    FiniteDimensional ℝ (Matrix (Fin l) (Fin m) ℝ) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin l → Fin m → ℝ))

/-- The norm-topology on `Matrix (Fin l) (Fin m) ℝ` is the canonical pi (product) topology (`rfl`):
the pi-norm structure introduces no competing topology. -/
theorem instTopologicalSpaceMatrix_eq_norm (l m : ℕ) :
    (instNormedAddCommGroupMatrix l m).toMetricSpace.toUniformSpace.toTopologicalSpace
      = (Pi.topologicalSpace : TopologicalSpace (Fin l → Fin m → ℝ)) := rfl

/-! ## Matrix multiplication as a continuous bilinear map -/

/-- Left-multiplication `B ↦ A·B` as a CLM (finite-dimensional ⟹ continuous). The inner factor of
the bilinear matrix-mult CLM. -/
noncomputable def mulLeftCLM (l m n : ℕ) (A : Matrix (Fin l) (Fin m) ℝ) :
    Matrix (Fin m) (Fin n) ℝ →L[ℝ] Matrix (Fin l) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => A * B, map_add' := fun x y => Matrix.mul_add A x y,
      map_smul' := fun a x => Matrix.mul_smul A a x }

@[simp] theorem mulLeftCLM_apply (l m n : ℕ) (A : Matrix (Fin l) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) : mulLeftCLM l m n A B = A * B := rfl

/-- **Matrix multiplication as a continuous bilinear map** `(A, B) ↦ A·B` (`Fin l × Fin m`, `Fin m ×
Fin n`). Built layered: the inner `mulLeftCLM A` (continuous, finite-dim), then the outer `A ↦
mulLeftCLM A` made continuous. -/
noncomputable def matMulBilin (l m n : ℕ) :
    Matrix (Fin l) (Fin m) ℝ →L[ℝ] Matrix (Fin m) (Fin n) ℝ →L[ℝ] Matrix (Fin l) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := mulLeftCLM l m n
      map_add' := fun A₁ A₂ => by ext B; simp [mulLeftCLM_apply, Matrix.add_mul]
      map_smul' := fun a A => by ext B; simp [mulLeftCLM_apply, Matrix.smul_mul] }

@[simp] theorem matMulBilin_apply (l m n : ℕ) (A : Matrix (Fin l) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) : matMulBilin l m n A B = A * B := rfl

/-! ## The matrix product rule -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The matrix product rule**: if `f`, `g` (matrix-valued, composable) have fderivs `f'`, `g'` at
`x`, then `fun y => f y * g y` has fderiv `(matMulBilin).precompR _ (f x) g' + .precompL _ f' (g x)`
at `x`. The composable shape (`l×m`, `m×n`) of `ContinuousLinearMap.hasFDerivAt_of_bilinear` for
`matMulBilin`. -/
theorem HasFDerivAt.matMul {l m n : ℕ} {f : G → Matrix (Fin l) (Fin m) ℝ}
    {g : G → Matrix (Fin m) (Fin n) ℝ} {f' : G →L[ℝ] Matrix (Fin l) (Fin m) ℝ}
    {g' : G →L[ℝ] Matrix (Fin m) (Fin n) ℝ} {x : G}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => f y * g y)
      ((matMulBilin l m n).precompR G (f x) g' + (matMulBilin l m n).precompL G f' (g x)) x := by
  have h := ContinuousLinearMap.hasFDerivAt_of_bilinear (B := matMulBilin l m n) hf hg
  simp only [matMulBilin_apply] at h
  exact h

end DLNFibre.DLN.RLCT
