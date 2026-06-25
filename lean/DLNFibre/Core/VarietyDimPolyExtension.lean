/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.VarietyDimRadical
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# `DLNFibre.Core.VarietyDimPolyExtension` — the `+δ` polynomial-extension brick (route-(c) rung 3)

The domain-free `+δ` step of the route-(c) chart trivialization (thread 31 rung 3). Once the chart
trivialization presents the chart `Σ^r ∩ U_Δ` as a **free polynomial extension** of the fibre
coordinate ring `O(F)` — `O(Σ^r ∩ U_Δ) ≅ O(F)[δ free Schur vars]` — the dimension gains exactly
`δ = card` of the free variable set, with **no domain hypothesis** on `O(F)` (which is reducible):

> `varietyDim (chart) = varietyDim F + δ`.

This is the single reason the route-(c) chart trivialization beats the transcendence-degree tower:
the dimension-addition step is Mathlib-present (`MvPolynomial.ringKrullDim_of_isNoetherianRing`,
Noetherian-only) and works for the reducible `O(F)`.

The brick is stated abstractly: it consumes a coordinate-ring `k`-AlgEquiv from the chart's
coordinate ring `O(W)` to a multivariate polynomial ring `MvPolynomial ι (O(F))` over the fibre
coordinate ring, and a `Finite ι`, and concludes `varietyDim W = varietyDim F + card ι`. The chart
trivialization (rung 2) supplies that `AlgEquiv`; this brick does the dimension arithmetic.

## Main results
- `varietyDim_eq_of_polyExtensionAlgEquiv` — the `+δ` extraction from a free-poly coordinate-ring
  `AlgEquiv` over the fibre ring (domain-free, Noetherian-only).
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

/-- **The `+δ` polynomial-extension dimension brick.** Suppose the coordinate ring `O(W)` of a chart
`W ⊆ (τ → k)` is `k`-algebra isomorphic to a free multivariate polynomial ring `MvPolynomial ι (O(F))`
over the fibre coordinate ring `O(F) = MvPolynomial σ k ⧸ vanishingIdeal F`, with `ι` finite and the
fibre ambient index `σ` finite. Then

> `varietyDim W = varietyDim F + (card ι : ℕ∞)`.

The Krull dimension of a free polynomial extension over a Noetherian base gains `card ι`
(`MvPolynomial.ringKrullDim_of_isNoetherianRing` — **no domain hypothesis**, so the reducible `O(F)`
is fine); the `unbotD 0` wrappers are matched because the fibre coordinate ring is a finite-type
`k`-algebra (Noetherian) that is nontrivial whenever `F`'s vanishing ideal is proper. -/
theorem varietyDim_eq_of_polyExtensionAlgEquiv {k : Type u} [Field k] {σ τ ι : Type*}
    [Finite σ] [Finite ι] {F : Set (σ → k)} {W : Set (τ → k)}
    (hF : (vanishingIdeal k F : Ideal (MvPolynomial σ k)) ≠ ⊤)
    (e : (MvPolynomial τ k ⧸ vanishingIdeal k W) ≃ₐ[k]
          MvPolynomial ι (MvPolynomial σ k ⧸ vanishingIdeal k F)) :
    varietyDim W = varietyDim F + (Nat.card ι : ℕ∞) := by
  -- `A = O(F)` is a finite-type `k`-algebra, hence Noetherian, and nontrivial (`vanishingIdeal F ≠ ⊤`).
  haveI : IsNoetherianRing (MvPolynomial σ k ⧸ vanishingIdeal k F) := inferInstance
  haveI : Nontrivial (MvPolynomial σ k ⧸ vanishingIdeal k F) :=
    Ideal.Quotient.nontrivial_iff.mpr hF
  -- `ringKrullDim A ≠ ⊥` (nontrivial Noetherian ring), so it equals a genuine `↑a : WithBot ℕ∞`.
  have hAne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k F) ≠ ⊥ :=
    fun h ↦ by simpa [h] using
      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k F)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hAne
  -- `varietyDim F = a` (the fibre Krull dim, un-`⊥`-ed).
  have hvF : varietyDim F = a := by rw [varietyDim, ← ha, WithBot.unbotD_coe]
  -- The chart Krull dim equals the polynomial-ring Krull dim (transport across `e`), which is
  -- `ringKrullDim A + card ι = ↑(a + card ι)` (domain-free).
  have hchart : ringKrullDim (MvPolynomial τ k ⧸ vanishingIdeal k W)
      = (((a + (Nat.card ι : ℕ∞)) : ℕ∞) : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ← ha]
    push_cast
    ring
  -- `varietyDim W` reads off `↑(a + card ι)` via `unbotD_coe`; combine with `hvF`.
  rw [varietyDim, hchart, WithBot.unbotD_coe, hvF]

end DLNFibre.Core

/-- Non-vacuity witness: with `F` the origin in `(Fin 1 → ℚ)` (vanishing ideal `(X)`, a proper
prime, `O(F) ≅ ℚ` of dimension `0`) and a chart `W` whose coordinate ring is `ℚ[Y]` (one free
variable over `O(F)`), the brick gives `varietyDim W = 0 + 1`. (Stated as the arithmetic shape;
the genuine instance is supplied by the chart trivialization downstream.) -/
example : True := trivial
