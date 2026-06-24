/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.NullstellensatzCodim
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# `DLNFibre.Core.VarietyDimRadical` — `varietyDim`/`ringKrullDim` is radical-insensitive

The formal linchpin of the route-(c) non-circularity de-risk (thread 31). The earlier scheme-level
product-iso route (R2-3b-4) was circular *for reducedness*: the forward map needed the strict ideal
inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
(`varietyDim Σ^r = δ + varietyDim F`) never touches that question, because `varietyDim` reads only
the **reduced / closed-set** structure: `ringKrullDim (R ⧸ I)` depends on `I` only through its
radical (both quotients have the same prime spectrum). So the route-(c) dimension build works
through `vanishingIdeal` (radical by construction) and never needs `fibreGenIdeal` to be radical.

A companion `varietyDim` invariance, the foundation of the route-(c) chart trivialization
(thread 31 rung 2): `varietyDim` transports across a **coordinate-ring `AlgEquiv`**
(`varietyDim_eq_of_coordRingAlgEquiv`) — even between varieties in *different* ambient affine
spaces. A regular isomorphism of affine varieties induces such an `AlgEquiv`, so this is the bridge
that carries the pivot-chart trivialization `mult⁻¹(U) ∩ Σ^r ≅ U × F` to a `varietyDim` equality
without ever realizing both sides in one ambient space.

## Main results
- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
- `ringKrullDim_quotient_eq_of_radical_eq` — same Krull dim for two ideals with equal radical.
- `varietyDim_eq_of_coordRingAlgEquiv` — `varietyDim` transport across a coordinate-ring `AlgEquiv`.
-/

namespace DLNFibre.Core

open PrimeSpectrum MvPolynomial

universe u

/-- **Radical-insensitivity of the quotient Krull dimension.** `ringKrullDim (R ⧸ I)` depends on `I`
only through its radical: `Spec (R ⧸ I) = zeroLocus I = zeroLocus I.radical = Spec (R ⧸ I.radical)`
as ordered sets, and Krull dimension is a spectrum invariant. -/
theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

/-- Two ideals with the same radical give the same quotient Krull dimension — the form the route-(c)
fibre-dimension build consumes (it reads `varietyDim` off `vanishingIdeal`, while a chart
presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
theorem ringKrullDim_quotient_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I.radical = J.radical) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J) := by
  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]

/-- **`varietyDim` transports across a coordinate-ring `AlgEquiv`.** If the coordinate rings
`MvPolynomial σ k ⧸ vanishingIdeal Z` and `MvPolynomial τ k ⧸ vanishingIdeal W` are `k`-algebra
isomorphic (the algebraic content of a regular isomorphism `Z ≅ W` of affine varieties, possibly in
different ambient spaces `σ`, `τ`), then `varietyDim Z = varietyDim W`. The Krull dimension is a
ring-isomorphism invariant (`ringKrullDim_eq_of_ringEquiv`); the `unbotD 0` wrapper is preserved. -/
theorem varietyDim_eq_of_coordRingAlgEquiv {k : Type u} [Field k] {σ τ : Type u}
    {Z : Set (σ → k)} {W : Set (τ → k)}
    (e : (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≃ₐ[k]
          (MvPolynomial τ k ⧸ vanishingIdeal k W)) :
    varietyDim Z = varietyDim W := by
  unfold varietyDim
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]

/-- **`ringKrullDim` of a quotient is invariant under a ring automorphism applied to the ideal.**
For a `RingEquiv e : T ≃+* T` and an ideal `I`, `ringKrullDim (T ⧸ I) = ringKrullDim (T ⧸ I.map e)`
— the quotient by the image ideal is isomorphic to the original quotient (`Ideal.quotientEquiv`).
This is the free half of the chart route: applying the normalizing gauge `AlgEquiv` to the chart
ideal preserves the chart dimension, so the work is only to identify the *gauged* ideal, not to
recompute its dimension. -/
theorem ringKrullDim_quotient_map_ringEquiv {T : Type*} [CommRing T] (e : T ≃+* T) (I : Ideal T) :
    ringKrullDim (T ⧸ I) = ringKrullDim (T ⧸ I.map (e : T →+* T)) :=
  ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I (I.map e) e rfl)

end DLNFibre.Core

/-- Non-vacuity witness: in `ℚ[X]`, the square `(X)^2` of the prime `(X)` shares its radical, so the
two quotient Krull dimensions agree — a genuinely non-reduced ideal `(X)^2` reduced to `(X)` without
changing the dimension. -/
example :
    ringKrullDim (Polynomial ℚ ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ)) ^ 2)
      = ringKrullDim (Polynomial ℚ ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) := by
  apply DLNFibre.Core.ringKrullDim_quotient_eq_of_radical_eq
  exact Ideal.radical_pow (I := (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) (by norm_num)
