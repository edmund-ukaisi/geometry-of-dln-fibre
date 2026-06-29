/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Set.Card

/-!
# `DLNFibre.Core.MinimalPrime.TopDimensional` — top-dimensional minimal primes

A minimal prime `p` of a commutative ring `A` is **top-dimensional** when the quotient `A ⧸ p`
realises the full Krull dimension of `A`:

> `Ideal.TopDimMinPrimes A := {p ∈ minimalPrimes A | ringKrullDim (A ⧸ p) = ringKrullDim A}`.

These are the irreducible components of `Spec A` of maximal dimension. In a catenary/affine setting
(where `codim = height`) this is equivalently the minimal-codimension condition — the codimension of
`V(p)` is minimal exactly when `dim (A ⧸ p)` is maximal; that codim = height identification needs
catenarity and is supplied under polynomial/catenary hypotheses by `Core.MinimalPrime.Bridge`. The
definition here is the **dimension-only** condition `ringKrullDim (A ⧸ p) = ringKrullDim A`, which
makes no catenary assumption.

It is the **transport-clean** reading of "top-dimensional component": a ring isomorphism
`e : A ≃+* B` carries `TopDimMinPrimes` bijectively by `Ideal.comap e` (minimal-prime membership
transports by `comap` along the surjection, and the quotient Krull dimension transports because
`A ⧸ p.comap e ≃+* B ⧸ p` and `ringKrullDim A = ringKrullDim B`). Hence the **count**
`(TopDimMinPrimes A).ncard` is a ring-isomorphism invariant
(`Ideal.topDimMinPrimes_ncard_eq_of_ringEquiv`) — and, since inverting a unit is an isomorphism, it
is invisible to unit-localizations too.

This module is pure commutative algebra. It lives in namespace `Ideal` and mirrors the Mathlib home
`Mathlib.RingTheory.Ideal.MinimalPrime` (a plausible `…/MinimalPrime/TopDimensional.lean`), so an
upstream move is a file-move with no namespace surgery.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace Ideal

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]

/-- **Top-dimensional minimal primes.** The minimal primes `p` of `A` whose quotient `A ⧸ p`
realises the full Krull dimension `ringKrullDim A` — the irreducible components of `Spec A` of
maximal dimension. The dimension-only condition (no catenary assumption); in a catenary/affine
setting it coincides with minimal codimension via `codim = height` (`Core.MinimalPrime.Bridge`). -/
def TopDimMinPrimes (A : Type*) [CommRing A] : Set (Ideal A) :=
  {p | p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A}

theorem mem_topDimMinPrimes {p : Ideal A} :
    p ∈ TopDimMinPrimes A ↔
      p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A := Iff.rfl

/-- A top-dimensional minimal prime is prime. -/
theorem isPrime_of_mem_topDimMinPrimes {p : Ideal A} (hp : p ∈ TopDimMinPrimes A) : p.IsPrime :=
  hp.1.1.1

/-! ## Transport along a ring isomorphism

A `RingEquiv e : A ≃+* B` carries `minimalPrimes` bijectively via `Ideal.comap e : Ideal B →
Ideal A`, which restricts to a bijection `TopDimMinPrimes B ≃ TopDimMinPrimes A` and preserves the
quotient Krull dimension via the induced quotient isomorphism. So `TopDimMinPrimes` transports as a
set-image and its `ncard` is preserved. -/

/-- `Ideal.comap e` of a top-dimensional minimal prime of `B` is one of `A`, for a ring iso
`e : A ≃+* B`. The minimal-prime membership is `Ideal.comap_minimalPrimes_eq_of_surjective`
(`e` surjective); the quotient Krull dimension is preserved because `A ⧸ p.comap e ≃+* B ⧸ p`
and `ringKrullDim A = ringKrullDim B`. -/
theorem comap_mem_topDimMinPrimes (e : A ≃+* B) {p : Ideal B} (hp : p ∈ TopDimMinPrimes B) :
    p.comap (e : A →+* B) ∈ TopDimMinPrimes A := by
  obtain ⟨hpmin, hpdim⟩ := hp
  refine ⟨?_, ?_⟩
  · -- `comap` of a minimal prime along a surjection is minimal over the comapped ideal `⊥`
    have : p.comap (e : A →+* B) ∈ ((⊥ : Ideal B).comap (e : A →+* B)).minimalPrimes := by
      rw [Ideal.comap_minimalPrimes_eq_of_surjective e.surjective]
      exact ⟨p, hpmin, rfl⟩
    rwa [Ideal.comap_bot_of_injective (e : A →+* B) e.injective] at this
  · -- `A ⧸ p.comap e ≃+* B ⧸ p` (quotient by a comapped ideal along a surjection)
    have hquot : ringKrullDim (A ⧸ p.comap (e : A →+* B)) = ringKrullDim (B ⧸ p) :=
      ringKrullDim_eq_of_ringEquiv
        (Ideal.quotientEquiv (p.comap (e : A →+* B)) p e (by
          rw [Ideal.map_comap_of_surjective (e : A →+* B) e.surjective]))
    rw [hquot, hpdim, ringKrullDim_eq_of_ringEquiv e]

/-- `Ideal.comap e` restricted to `TopDimMinPrimes B` is a bijection onto `TopDimMinPrimes A`, for a
ring iso `e : A ≃+* B` — the two-sided inverse is `comap e.symm`. -/
theorem bijOn_comap_topDimMinPrimes (e : A ≃+* B) :
    Set.BijOn (Ideal.comap (e : A →+* B)) (TopDimMinPrimes B) (TopDimMinPrimes A) := by
  refine ⟨fun p hp ↦ comap_mem_topDimMinPrimes e hp, ?_, ?_⟩
  · -- InjOn: `comap e` is injective (`e` surjective)
    exact fun p _ q _ hpq ↦ Ideal.comap_injective_of_surjective _ e.surjective hpq
  · -- SurjOn: `q ∈ TopDimMinPrimes A` is `comap e (map e q)` with `map e q ∈ TopDimMinPrimes B`
    intro q hq
    refine ⟨q.map (e : A →+* B), ?_, ?_⟩
    · have := comap_mem_topDimMinPrimes e.symm (A := B) (B := A) (p := q) hq
      rwa [show (q.comap (e.symm : B →+* A)) = q.map (e : A →+* B) from
        Ideal.comap_symm (I := q) e] at this
    · exact Ideal.comap_map_of_bijective (e : A →+* B) e.bijective

/-- The top-dimensional minimal-prime count is a ring-isomorphism invariant. -/
theorem topDimMinPrimes_ncard_eq_of_ringEquiv (e : A ≃+* B) :
    (TopDimMinPrimes A).ncard = (TopDimMinPrimes B).ncard :=
  (bijOn_comap_topDimMinPrimes e).ncard_eq.symm

end Ideal
