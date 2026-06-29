import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.Basic

/-!
# `RouteMFrameLocality` — b-FrameM-3 keystone: value-level coordinate-locality ⟹ fderiv block-triangular

The load-bearing bridge of the Route (b) det_comp ladder (`item3-frameM-buildspec.md` b-FrameM-3, the
RISK piece): lift the PROVEN value-level off-block-vanishing (`Agen_genBlkFlatStruct_reads_le`,
`RouteMLayerGrade`: the chart's output at layer `s` reads only input layers `≤ s`) to the
**fderiv-level** off-block-vanishing — i.e. `DFrame_M`'s standard-basis matrix is block-triangular
under the layer grading. This is the `hbt` hypothesis the interior-det headline
(`interiorDet_headline_of_blockTri`) consumes.

The calculus fact: a function whose `i`-th output coordinate is **invariant** under changing the
`j`-th input coordinate has `∂(output i)/∂(input j) = 0`. Proof: the line `t ↦ u + t·eⱼ` carries
`v ↦ f v i` to a constant, so its directional derivative `(D eⱼ) i` is `0`. NO entrywise computation
of `DFrame_M` — the off-block-vanishing INHERITS the value-level locality, network-free and cast-light
(the genuine soundness — the locality — is already proven at the value level).

* `fderiv_apply_single_proj_zero_of_indep` — `(D eⱼ) i = 0` when `f`'s `i`-th output coord is invariant
  under changing input coord `j` (the per-output-coordinate keystone).
* `toMatrix_blockTriangular_of_locality` — given the per-output-coord locality `g i < g j ⟹ output i
  invariant under input j`, the standard-basis matrix `toMatrix' D` is `BlockTriangular (toDual ∘ g)`
  (the LOWER-triangular form the verdict names; the entry `(i,j)` vanishes when `g j > g i`).

These are network-free (Mathlib calculus + matrix only), so they apply to ANY differentiable
self-map of `Fin N → ℝ` with the coordinate-locality — in particular `DFrame_M = fderiv phiFlatLiveR1`
once its `HasFDerivAt` is established (the remaining b-FrameM-2 differentiability piece).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-- **The per-output-coordinate fderiv-locality keystone.** If `f : (Fin N → ℝ) → (Fin N → ℝ)` has
`HasFDerivAt f D u`, and the `i`-th output coordinate of `f` is INVARIANT under changing the `j`-th
input coordinate (`f v i = f u i` whenever `v` agrees with `u` off coordinate `j`), then the
directional derivative `(D eⱼ) i = 0`. The directional derivative of the scalar `v ↦ f v i` along the
`j`-th coordinate line `t ↦ u + t·eⱼ` is `0` because that scalar is constant on the line. -/
theorem fderiv_apply_single_proj_zero_of_indep {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (u : Fin N → ℝ) (hf : HasFDerivAt f D u) (i j : Fin N)
    (hinv : ∀ v : Fin N → ℝ, (∀ k, k ≠ j → v k = u k) → f v i = f u i) :
    (D ((Pi.single j (1:ℝ) : Fin N → ℝ))) i = 0 := by
  set e : Fin N → ℝ := Pi.single j (1:ℝ) with he
  -- the scalar `i`-th output coord, with fderiv `proj i ∘ D`.
  set fi : (Fin N → ℝ) → ℝ := (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ) ∘ f with hfi
  set Di : (Fin N → ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).comp D with hDi
  have hfderiv_i : HasFDerivAt fi Di u :=
    (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp u hf
  -- the coordinate line `t ↦ u + t·eⱼ`, derivative `eⱼ` at `0`.
  have h1 : HasDerivAt (fun t : ℝ => t • e) e 0 := by
    have := (hasDerivAt_id (0:ℝ)).smul_const e; simpa using this
  have hline : HasDerivAt (fun t : ℝ => u + t • e) e 0 := by
    have h := (hasDerivAt_const (0:ℝ) u).add h1; simp only [zero_add] at h; exact h
  have hfu : HasFDerivAt fi Di ((fun t : ℝ => u + t • e) 0) := by
    have : (fun t : ℝ => u + t • e) 0 = u := by simp
    rw [this]; exact hfderiv_i
  -- the composite `t ↦ f (u + t·eⱼ) i` has derivative `Di eⱼ` at `0` …
  have hcomp : HasDerivAt (fi ∘ (fun t : ℝ => u + t • e)) (Di e) 0 := hfu.comp_hasDerivAt 0 hline
  -- … but it is the constant `f u i`, so the derivative is `0`.
  have hconst : (fi ∘ (fun t : ℝ => u + t • e)) = fun _ => fi u := by
    funext t
    change f (u + t • e) i = f u i
    apply hinv; intro k hk; simp [he, hk]
  rw [hconst] at hcomp
  have hzero : Di e = 0 := hcomp.unique (hasDerivAt_const (0:ℝ) (fi u))
  simpa [hDi] using hzero

/-- **b-FrameM-3: value-level locality ⟹ `DFrame` block-triangular.** Given a differentiable self-map
`f` of `Fin N → ℝ` (`HasFDerivAt f D u`) and a grading `g : Fin N → ℕ` such that the `i`-th output
coordinate is invariant under changing any input coordinate `j` at a STRICTLY HIGHER grade
(`g i < g j` — the b-0 "output layer `i` reads only layers `≤ g i`" locality), the standard-basis
matrix `toMatrix' D` is `BlockTriangular (OrderDual.toDual ∘ g)`: its entry `(i,j)` vanishes whenever
`g j > g i`. This is the `hbt` input of `interiorDet_headline_of_blockTri`, INHERITED from the proven
value-level locality (no entrywise `DFrame` computation). -/
theorem toMatrix_blockTriangular_of_locality {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (u : Fin N → ℝ) (hf : HasFDerivAt f D u)
    (g : Fin N → ℕ)
    (hloc : ∀ i j : Fin N, g i < g j →
      ∀ v : Fin N → ℝ, (∀ k, k ≠ j → v k = u k) → f v i = f u i) :
    (LinearMap.toMatrix' (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))).BlockTriangular
      (OrderDual.toDual ∘ g) := by
  intro i j hij
  have hgij : g i < g j := OrderDual.toDual_lt_toDual.mp hij
  rw [LinearMap.toMatrix'_apply]
  exact fderiv_apply_single_proj_zero_of_indep f D u hf i j (hloc i j hgij)

/-! ## Non-vacuity: the keystone fires, and the block-triangularity is genuine -/

/-- **Non-vacuity of the keystone.** A constant map has every output coordinate invariant under every
input coordinate, so `(D eⱼ) i = 0` for its (zero) fderiv — the keystone fires (and gives the right
answer: the zero map has zero entries). Confirms the hypothesis is satisfiable. -/
example {N : ℕ} (c : Fin N → ℝ) (u : Fin N → ℝ) (i j : Fin N) :
    ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) ((Pi.single j (1:ℝ) : Fin N → ℝ))) i = 0 :=
  fderiv_apply_single_proj_zero_of_indep (fun _ => c) 0 u (hasFDerivAt_const c u) i j
    (fun _ _ => rfl)

/-- **Non-vacuity of the block-triangularity.** A constant map is block-triangular under any grading
(every output is invariant under every input) — the corollary fires. -/
example {N : ℕ} (c : Fin N → ℝ) (u : Fin N → ℝ) (g : Fin N → ℕ) :
    (LinearMap.toMatrix' ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :
      (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))).BlockTriangular (OrderDual.toDual ∘ g) :=
  toMatrix_blockTriangular_of_locality (fun _ => c) 0 u (hasFDerivAt_const c u) g
    (fun _ _ _ _ _ => rfl)

end DLNFibre.DLN.RLCT
