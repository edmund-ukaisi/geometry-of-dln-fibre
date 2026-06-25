/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.VarietyDimRadical
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# `DLNFibre.Core.PrincipalOpenComorphism` — descend a regular map of principal opens to coordinate rings

The abstract de-risk crux of the route-(c) localized chart `AlgEquiv` (thread 31, the hard rung):
turn a **regular map of principal opens** `D(f) ∩ Z → W` of affine varieties into a `k`-algebra
hom of the **localized** coordinate rings `O(W) → O(Z)[1/f]`, with the `vanishingIdeal` descent
discharged by the *point-realization* universal property, never a strict generator-ideal
containment (the R2-3b-4 wall the route avoids).

Setup. `Z ⊆ (σ → k)`, `W ⊆ (τ → k)` are subsets of affine spaces, `OZ = MvPolynomial σ k ⧸
vanishingIdeal Z`, `OW = MvPolynomial τ k ⧸ vanishingIdeal W`, and `f : OZ` a localizing element.
A regular map `D(f) ∩ Z → W` is, comorphically, a family of denominator-bounded fractions — but the
clean realization is a substitution `ν : τ → Localization.Away f` together with the geometric fact
that `ν` *evaluates as the point map*: for every `x ∈ Z` with `f(x) ≠ 0`, the substituted value of
each coordinate `ν j`, read at `x`, is the `j`-coordinate of the image point `ρ(x) ∈ W`.

The descent. `aeval ν : MvPolynomial τ k →ₐ[k] Localization.Away f` kills `vanishingIdeal W`: a
`p` vanishing on `W` has `aeval ν p` vanishing at every point of `D(f) ∩ Z` (it equals `aeval (ρ x)
p = 0`), and a regular function on the principal open `D(f)` of the (reduced) variety `Z` that
vanishes on the dense `D(f) ∩ Z` is `0` in `O(Z)[1/f]` — this last step is the clearing-denominators
fact `IsLocalization.mk'_eq_zero_iff`, *not* a generator-ideal claim.

This module proves the abstract descent; the chart instantiation (`ν` = the Schur/gauge substitution)
is downstream. Kept network-free and chart-free so it is reusable for both the `Ψ` and `Φ` directions.

## Main results
- `away_eq_zero_of_mul_pow_mem_vanishingIdeal` — clearing-denominators: a fraction over `O(Z)` is
  `0` in `O(Z)[1/f]` iff some `f`-power times its numerator lies in `vanishingIdeal Z`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- **Clearing denominators in the away-localization of a coordinate ring.** For `Z ⊆ (σ → k)`,
the coordinate ring `OZ = MvPolynomial σ k ⧸ vanishingIdeal Z`, and a localizing element `f : OZ`
with lift `f₀ : MvPolynomial σ k` (`Quotient.mk _ f₀ = f`): a class `Quotient.mk _ a` over `OZ`
becomes `0` in `Localization.Away f` exactly when some `f`-power kills it, i.e.
`Quotient.mk _ (f₀^n * a) ∈ ⊥`, equivalently `f₀^n * a ∈ vanishingIdeal Z`.

This is the route's *only* bridge from "vanishes on the principal open `D(f) ∩ Z`" to "is `0` in
`O(Z)[1/f]`": no strict generator-ideal containment, only `IsLocalization.mk'_eq_zero_iff` over the
reduced quotient. -/
theorem away_eq_zero_iff_exists_pow_mul_mem {σ : Type u} (Z : Set (σ → k))
    (f₀ a : MvPolynomial σ k) :
    (IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk (vanishingIdeal k Z) f₀))
        (Ideal.Quotient.mk (vanishingIdeal k Z) a)
        (1 : Submonoid.powers (Ideal.Quotient.mk (vanishingIdeal k Z) f₀)) = 0)
      ↔ ∃ n : ℕ, f₀ ^ n * a ∈ vanishingIdeal k Z := by
  rw [IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨s, m, hm⟩, hs⟩
    -- `s = (mk f₀)^m`, and `s * (mk a) = 0` in `OZ`, i.e. `(mk f₀)^m * mk a = mk (f₀^m * a) = 0`.
    refine ⟨m, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
    simpa [← hm] using hs
  · rintro ⟨n, hn⟩
    refine ⟨⟨(Ideal.Quotient.mk (vanishingIdeal k Z) f₀) ^ n, n, rfl⟩, ?_⟩
    change (Ideal.Quotient.mk (vanishingIdeal k Z) f₀) ^ n
        * (Ideal.Quotient.mk (vanishingIdeal k Z) a) = 0
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hn

end DLNFibre.Core
