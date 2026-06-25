/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreNormalForm
import DLNFibre.Core.VarietyDimRadical

/-!
# `DLNFibre.Core.VarietyDimBaseChange` — `varietyDim` is invariant under the base-change action

The `varietyDim` analogue of the engine's `codimRep_baseChange_image` (`FibreNormalForm`): the
variety dimension of a subset of `Rep_d` is unchanged when it is translated by an endpoint
base-change `A ↦ P • A`. This is the generator-free transport the route-(c) chart trivialization
leans on — `vanishingIdeal` of the translated set is the `comap` of the original's vanishing ideal
along the base-change ring isomorphism (`vanishingIdeal_image_smul`), and a quotient by a `comap`
ideal along a `RingEquiv` has the same Krull dimension (`ringKrullDim_quotient_comap_ringEquiv`).
No determinantal-ideal generators enter.

## Main results
- `varietyDim_baseChange_image` — `varietyDim ((P • ·) '' Z) = varietyDim Z`.
- `varietyDim_fibre_endpoint_conj_eq` — every endpoint-conjugate rank-`r` fibre has the same
  `varietyDim` as `fibre E` (the constant-fibre-dimension fact the sweep fibration consumes).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **`varietyDim` invariance under a base change.** The variety dimension at the canonical
flattening is invariant under the linear automorphism `A ↦ P • A`: `varietyDim ((P • ·) '' Z) =
varietyDim Z`. The shifted vanishing ideal is the `comap` of the original along the base-change ring
isomorphism (`vanishingIdeal_image_smul`); `ringKrullDim_quotient_comap_ringEquiv` preserves the
Krull dimension. Generator-free — no determinantal-ideal generation is invoked. -/
theorem varietyDim_baseChange_image [Infinite k] (d : Fin (N + 1) → ℕ)
    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
    varietyDim (canonicalCoord d '' ((fun A ↦ P • A) '' Z))
      = varietyDim (canonicalCoord d '' Z) := by
  unfold varietyDim
  rw [vanishingIdeal_image_smul]
  congr 1
  exact ringKrullDim_quotient_comap_ringEquiv (baseChangeAlgEquiv P).toRingEquiv
    (vanishingIdeal k (canonicalCoord d '' Z))

/-- **Constant fibre dimension along the endpoint orbit.** Every endpoint-conjugate
`fibre d (P_N · E · P_0⁻¹)` (a rank-`r` fibre, `= (P • ·) '' (fibre d E)` by `image_smul_fibre`) has
the same `varietyDim` as `fibre d E`. This is the geometric input that makes the homogeneous sweep
`Σ^r = ⋃_P (P • ·) '' (fibre E)` a constant-fibre-dimension fibration — no Chevalley/semicontinuity,
just base-change invariance of `varietyDim`. -/
theorem varietyDim_fibre_endpoint_conj_eq [Infinite k] (d : Fin (N + 1) → ℕ)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (P : BaseChangeGroup (k := k) d) :
    varietyDim (canonicalCoord d ''
        (fibre d (Units.val (P (Fin.last N)) * E * Units.val ((P 0)⁻¹))))
      = varietyDim (canonicalCoord d '' (fibre d E)) := by
  rw [← image_smul_fibre]
  exact varietyDim_baseChange_image d P (fibre d E)

end DLNFibre.Core
