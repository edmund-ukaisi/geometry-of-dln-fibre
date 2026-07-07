import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Data.Matrix.Bilinear
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiStrictDeriv` — the strict-derivative scaffold for the
absorbing diffeo `Ψ` (#120 `hstep2`, piece 3)

The general-`L` absorbing diffeo `Ψ` acts, on each core coordinate, as `S ↦ (I − K)·S`, where the
left factor `I − K` equals the identity at the basepoint (the coupling `K` carries the vanishing core
factor, so `K(wstar) = 0`) and the right factor `S` vanishes at the basepoint (`S(wstar) = 0`, the
deepest core is `0`). The `dΨ(0) = I` fact then reduces to a single analytic mechanism, isolated here
and free of any DLN specifics:

  for a bounded bilinear map `B` and `x ↦ B (g x) (f x)` with `f x = 0`, the strict Fréchet
  derivative at `x` is `(B (g x)).comp f'` — the left-factor derivative term `B (g' ·) (f x)` drops
  because `f x = 0`.

Instantiated later (piece 5) with `B` = matrix multiplication, `g x = I − K(x)`, `f x = S(x)`: at the
basepoint `g x = I` so `B (g x) = id`, giving derivative `f'` on the core block; on the reg/spec blocks
`Ψ` is the identity; together `dΨ(wstar) = id`.

Pure Mathlib analysis (`ContinuousLinearMap.isBoundedBilinearMap` + `IsBoundedBilinearMap.deriv_apply`);
cites nothing.
-/

namespace DLNFibre.DLN.RLCT

open ContinuousLinearMap Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X E F G : Type*}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Bilinear strict derivative with a vanishing right factor** (the `dΨ(0)=I` mechanism). For a
bounded bilinear `B : E →L[𝕜] F →L[𝕜] G` and differentiable `g : X → E`, `f : X → F` with
`f x = 0`, the map `y ↦ B (g y) (f y)` has strict Fréchet derivative `(B (g x)).comp f'` at `x`
(the `B (g' ·) (f x)` term of the product rule drops because `f x = 0`). -/
theorem hasStrictFDerivAt_bilinear_of_right_zero
    (B : E →L[𝕜] F →L[𝕜] G) {g : X → E} {f : X → F} {g' : X →L[𝕜] E} {f' : X →L[𝕜] F} {x : X}
    (hg : HasStrictFDerivAt g g' x) (hf : HasStrictFDerivAt f f' x) (hf0 : f x = 0) :
    HasStrictFDerivAt (fun y => B (g y) (f y)) ((B (g x)).comp f') x := by
  -- The bounded bilinear map and its strict derivative at `(g x, f x)`.
  have hbil : HasStrictFDerivAt (fun p : E × F => B p.1 p.2)
      (B.isBoundedBilinearMap.deriv (g x, f x)) (g x, f x) :=
    B.isBoundedBilinearMap.hasStrictFDerivAt (g x, f x)
  -- Compose with `y ↦ (g y, f y)`; the composite derivative is
  -- `(B.isBoundedBilinearMap.deriv (g x, f x)).comp (g'.prod f')`.
  have hcomp := hbil.comp x (hg.prodMk hf)
  -- That derivative simplifies to `(B (g x)).comp f'` because `f x = 0` kills the `B (g' ·) (f x)` term.
  have hEq : (B (g x)).comp f'
      = (B.isBoundedBilinearMap.deriv (g x, f x)).comp (g'.prod f') := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      IsBoundedBilinearMap.deriv_apply, hf0, map_zero, add_zero]
  rw [hEq]
  exact hcomp

/-! ## The rectangular matrix-multiplication bounded-bilinear map

The left factor of the absorbing shear is a square matrix acting by left multiplication on the
rectangular core block. `matMulCLM` packages rectangular matrix multiplication as a
`ContinuousLinearMap`-valued `ContinuousLinearMap` (bounded bilinear, since the matrix spaces are
finite-dimensional), so the scaffold above applies with `B = matMulCLM`. At the identity left factor
it is the identity map (`matMulCLM_one`), which turns the scaffold's `(B (g x)).comp f'` into `f'`. -/

/-- **Rectangular matrix multiplication as a bounded-bilinear `ContinuousLinearMap`**:
`matMulCLM a b c P Q = P * Q`. Built from the matrix-multiplication bilinear `LinearMap` via the
finite-dimensional `LinearMap.toContinuousLinearMap` equivalence on the inner and outer factors. -/
noncomputable def matMulCLM (a b c : ℕ) :
    Matrix (Fin a) (Fin b) ℝ →L[ℝ] Matrix (Fin b) (Fin c) ℝ →L[ℝ] Matrix (Fin a) (Fin c) ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (Matrix (Fin b) (Fin c) ℝ →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ)
          ≃ₗ[ℝ] (Matrix (Fin b) (Fin c) ℝ →L[ℝ] Matrix (Fin a) (Fin c) ℝ)).toLinearMap.comp
      (mulLinearMap ℝ))

/-- `matMulCLM` computes matrix multiplication. -/
@[simp] theorem matMulCLM_apply {a b c : ℕ} (P : Matrix (Fin a) (Fin b) ℝ)
    (Q : Matrix (Fin b) (Fin c) ℝ) : matMulCLM a b c P Q = P * Q := by
  simp only [matMulCLM, LinearMap.coe_toContinuousLinearMap, LinearMap.coe_comp,
    Function.comp_apply]
  rfl

/-- Left multiplication by the identity matrix is the identity map: `matMulCLM 1 = id`. -/
theorem matMulCLM_one (a c : ℕ) :
    matMulCLM a a c 1 = ContinuousLinearMap.id ℝ (Matrix (Fin a) (Fin c) ℝ) := by
  refine ContinuousLinearMap.ext fun Q => ?_
  rw [matMulCLM_apply, Matrix.one_mul, ContinuousLinearMap.id_apply]

end DLNFibre.DLN.RLCT
