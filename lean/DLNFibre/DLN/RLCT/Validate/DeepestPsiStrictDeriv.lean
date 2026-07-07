import Mathlib.Analysis.Calculus.FDeriv.Bilinear

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

open ContinuousLinearMap

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

end DLNFibre.DLN.RLCT
