import DLNFibre.DLN.RLCT.Validate.RouteMFrameLocality
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDetHeadline

/-!
# `RouteMLocalityDet` — the reusable bridge: value-locality ⟹ Jacobian abs-det factorizes by grade

The clean composition that was missing between the two banked route-α levers: given a differentiable
self-map of `Fin N → ℝ` whose output coordinate `i` is invariant under any input coordinate `j` at a
strictly higher grade (`g i < g j`), its Jacobian determinant's absolute value is the product of the
diagonal-block determinants' absolute values — UNCONDITIONALLY (no per-block-det inputs, no map
equality). This is `toMatrix_blockTriangular_of_locality` (`RouteMFrameLocality`) fed straight into
the abs-form `Matrix.BlockTriangular.det`.

It is stated over the grading `OrderDual.toDual ∘ g` exactly as the locality keystone produces it
(`g i < g j ⟹ entry (i,j) = 0` is LOWER-triangular under `toDual`, matching the one-sided dependency
`RouteMLayerGrade`/`RouteMRoleGrade` prove); `ℕᵒᵈ` is a `LinearOrder`, so `BlockTriangular.det`
applies.

* `fderiv_abs_det_eq_prod_diagBlocks` — `|det (fderiv f u)| = ∏_{a ∈ image (toDual∘g)}
  |(toMatrix' D).toSquareBlock (toDual∘g) a).det|`, from value-locality + `HasFDerivAt`.

This is the UNCONDITIONAL det-factorizes-by-grade fact: it discharges the headline's `hbt` AND the
abs `BlockTriangular.det` step in one shot, leaving ONLY the per-block-det identifications (the
`hR`/`hB` engine values) and — for the real chart — the input/output grading alignment
(`paramsPack_layer`) to the wiring stage. See `RouteMRoleGrade`'s scope note for the recalibration.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

/-- **Value-locality ⟹ Jacobian abs-det factorizes by grade (UNCONDITIONAL).** For a differentiable
self-map `f` of `Fin N → ℝ` (`HasFDerivAt f D u`) and a grading `g : Fin N → ℕ` with the one-sided
dependency `g i < g j ⟹ output coord i invariant under input coord j`, the Jacobian determinant's
absolute value is the product of the diagonal-block determinants' absolute values, over the grading
`toDual ∘ g`. Composes `toMatrix_blockTriangular_of_locality` (block-triangularity from locality)
with the abs form of `Matrix.BlockTriangular.det`. No per-block-det input, no map equality — the
unconditional det-factorizes-by-grade fact the interior-det headline rests on. -/
theorem fderiv_abs_det_eq_prod_diagBlocks {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (u : Fin N → ℝ) (hf : HasFDerivAt f D u)
    (g : Fin N → ℕ)
    (hloc : ∀ i j : Fin N, g i < g j →
      ∀ v : Fin N → ℝ, (∀ k, k ≠ j → v k = u k) → f v i = f u i) :
    |LinearMap.det (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))|
      = ∏ a ∈ Finset.univ.image (OrderDual.toDual ∘ g),
          |((LinearMap.toMatrix' (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))).toSquareBlock
            (OrderDual.toDual ∘ g) a).det| := by
  have hbt := toMatrix_blockTriangular_of_locality f D u hf g hloc
  rw [← LinearMap.det_toMatrix' (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)), hbt.det, Finset.abs_prod]

/-! ## Non-vacuity: the bridge fires on a constant map (zero fderiv, every coord invariant)

A constant map has every output coordinate invariant under every input, so the locality hypothesis
is (vacuously) met and the bridge fires. Confirms the composed hypothesis is satisfiable end-to-end. -/

/-- **Non-vacuity.** The bridge fires for a constant map: every output is invariant under every
input, so the locality hypothesis holds and the abs-det equals the diagonal-block product. -/
example {N : ℕ} (c : Fin N → ℝ) (u : Fin N → ℝ) (g : Fin N → ℕ) :
    |LinearMap.det ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))|
      = ∏ a ∈ Finset.univ.image (OrderDual.toDual ∘ g),
          |((LinearMap.toMatrix' ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :
            (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))).toSquareBlock (OrderDual.toDual ∘ g) a).det| :=
  fderiv_abs_det_eq_prod_diagBlocks (fun _ => c) 0 u (hasFDerivAt_const c u) g
    (fun _ _ _ _ _ => rfl)

end DLNFibre.DLN.RLCT
