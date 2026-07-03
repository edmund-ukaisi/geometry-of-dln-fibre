import DLNFibre.DLN.RLCT.Validate.D1SecondPeelMinor
import DLNFibre.Core.ResidualRank

/-!
# `DLNFibre.DLN.RLCT.Validate.D1ResidualJacobianRank` — the `b1 → b2` Jacobian-rank bridge

The bridge that makes the network-free `b2` rank identity (`DLNFibre.Core.residual_finrank_eq`)
usable at the DLN second-peel gate `hrank₂`. Given that the first-peel slice residual `h = q (0,·)`
has a KNOWN Fréchet derivative `HasFDerivAt h L t0` at its basepoint (this is what the `b1`
derivative-exposing chart variant supplies), its residual Jacobian MATRIX `jacResid h t0`
(`D1SecondPeelMinor`) is exactly the coordinate matrix of `L`, so

    (jacResid h t0).rank = finrank ℝ (range L).

Combined with `b2` (`finrank (range L) = finrank (range T) − k` for the residual composite `L`) and
the middle-stratum count `finrank (range T) − k = extraCountRect …` (the `b3` piece), this discharges
`hrank₂` as `extraCountRect … ≤ (jacResid h t0).rank`.

## The identity

`jacResid h t0 i c = fderiv (fun t => h t i) t0 (Pi.single c 1)`. When `HasFDerivAt h L t0` with `L`
a CLM into `EuclideanSpace ℝ (Fin n)`, the `i`-th component map `fun t => h t i` has derivative
`(EuclideanSpace.proj i).comp L`, so `jacResid h t0 i c = L (Pi.single c 1) i`. That is the `(i,c)`
entry of `LinearMap.toMatrix'` of the pi-readout `Lpi := (EuclideanSpace.equiv (Fin n) ℝ) ∘ L`; and
`Matrix.rank (toMatrix' Lpi) = finrank (range Lpi) = finrank (range L)` (the Euclidean ≃ Pi iso
preserves the range's `finrank`).

Network-generic above the `HasFDerivAt` input; no DLN chart dependency here (the chart that PRODUCES
`HasFDerivAt h L t0` is the separate `b1` build).
-/

open Matrix Module LinearMap

namespace DLNFibre.DLN.RLCT

section Bridge

variable {N n : ℕ}

/-- The `i`-th component `fun t => h t i` of a map into `EuclideanSpace ℝ (Fin n)` has derivative
`(EuclideanSpace.proj i).comp L` when `HasFDerivAt h L t0`. -/
theorem hasFDerivAt_component_of_hasFDerivAt
    (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (L : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) (t0 : Fin N → ℝ)
    (hL : HasFDerivAt h L t0) (i : Fin n) :
    HasFDerivAt (fun t => h t i) ((EuclideanSpace.proj i).comp L) t0 :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t0 hL

/-- **The residual Jacobian entry from the derivative.** When `HasFDerivAt h L t0`, the `(i, c)`
entry of `jacResid h t0` is `L (Pi.single c 1) i`. -/
theorem jacResid_apply_of_hasFDerivAt
    (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (L : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) (t0 : Fin N → ℝ)
    (hL : HasFDerivAt h L t0) (i : Fin n) (c : Fin N) :
    jacResid h t0 i c = L (Pi.single c 1) i := by
  rw [jacResid_apply, (hasFDerivAt_component_of_hasFDerivAt h L t0 hL i).fderiv]
  rfl

/-- The pi-coordinate readout of `L`: `Lpi : (Fin N → ℝ) →ₗ (Fin n → ℝ)`, `Lpi x i = L x i`.
(`EuclideanSpace ℝ (Fin n)` is `PiLp 2`, so its `i`-th coordinate readout is a linear map to `ℝ`.) -/
noncomputable def euclidReadout (L : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  ((EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap).comp (L : (Fin N → ℝ) →ₗ[ℝ] _)

@[simp] theorem euclidReadout_apply (L : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : Fin N → ℝ) (i : Fin n) : euclidReadout L x i = L x i := rfl

/-- `range (euclidReadout L)` and `range L` have the same `finrank` (the Euclidean ≃ Pi iso). -/
theorem finrank_range_euclidReadout (L : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    finrank ℝ (LinearMap.range (euclidReadout L))
      = finrank ℝ (LinearMap.range (L : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) := by
  rw [euclidReadout, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv _

/-- The residual Jacobian IS the coordinate matrix of the derivative's pi-readout. -/
theorem jacResid_eq_toMatrix'_of_hasFDerivAt
    (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (L : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) (t0 : Fin N → ℝ)
    (hL : HasFDerivAt h L t0) :
    jacResid h t0 = LinearMap.toMatrix' (euclidReadout L) := by
  ext i c
  rw [jacResid_apply_of_hasFDerivAt h L t0 hL i c, LinearMap.toMatrix'_apply,
    euclidReadout_apply]

/-- **The `b1 → b2` Jacobian-rank bridge.** When the slice residual `h` has derivative `L` at `t0`
(`HasFDerivAt h L t0`), its residual-Jacobian matrix rank equals the rank of `L`:

    (jacResid h t0).rank = finrank ℝ (range L).

Feeds `b2`'s `finrank (range L)` into the DLN gate `hrank₂`, which is stated on `(jacResid h t0).rank`. -/
theorem jacResid_rank_eq_of_hasFDerivAt
    (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (L : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) (t0 : Fin N → ℝ)
    (hL : HasFDerivAt h L t0) :
    (jacResid h t0).rank
      = finrank ℝ (LinearMap.range (L : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) := by
  rw [jacResid_eq_toMatrix'_of_hasFDerivAt h L t0 hL]
  rw [Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix' (euclidReadout L))
      (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin N)),
    Matrix.toLin_eq_toLin', Matrix.toLin'_toMatrix']
  exact finrank_range_euclidReadout L

end Bridge

end DLNFibre.DLN.RLCT
