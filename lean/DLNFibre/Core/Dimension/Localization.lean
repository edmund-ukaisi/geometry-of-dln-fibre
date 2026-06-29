/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Krull dimension under localization (the `≤` half)

Localization never increases Krull dimension: for any localization `S = M⁻¹R` of a commutative ring
`R` at a submonoid `M`,

  `ringKrullDim S ≤ ringKrullDim R`.

The primes of `S` correspond order-isomorphically to the primes of `R` disjoint from `M`
(`IsLocalization.orderIsoOfPrime`), so `PrimeSpectrum.comap (algebraMap R S)` is a strict-monotone
injection of prime spectra (monotone as the `comap` of a ring hom, injective by
`PrimeSpectrum.localization_comap_injective`), and Krull dimension is monotone under strict-monotone
maps (`Order.krullDim_le_of_strictMono`).

The matching `≥` — the genuine *no-drop*, that inverting an element which avoids a top-dimensional
minimal prime does not drop the dimension — is the harder direction and is not part of this file;
this is the always-true `≤` half, reusable and domain-free.

This file mirrors the eventual Mathlib home `Mathlib.RingTheory.KrullDimension.Localization` (there is
no such file upstream at this pin — `RingTheory/KrullDimension/` has `{Basic,Field,LocalRing,Module,
NonZeroDivisors,PID,Polynomial,Regular,Zero}` but no `Localization`), placed in the project's
`DLNFibre.Core.Dimension` family beside the other Krull-dimension bricks so an upstream move is a
file-move with no namespace surgery. No `@[stacks ...]` tag is attached: the Stacks Project carries
this fact only through the prime-bijection of a localization (tag `00KD`), not as a standalone
dimension inequality, so a `@[stacks ...]` reference would overstate the match.

## Main results
- `ringKrullDim_localization_le` — `ringKrullDim S ≤ ringKrullDim R` for any localization
  `S = M⁻¹R`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open IsLocalization

namespace DLNFibre.Core.Dimension

universe u

variable {R : Type u} [CommRing R]

/-- **Localization does not increase Krull dimension.** For a localization `S = M⁻¹R`, the prime
spectrum of `S` order-embeds into that of `R` via `comap (algebraMap R S)`: this map is monotone (it
is the `comap` of a ring hom) and injective for a localization
(`PrimeSpectrum.localization_comap_injective`), hence strict-monotone, and Krull dimension is
monotone under strict-monotone maps (`Order.krullDim_le_of_strictMono`). So
`ringKrullDim S ≤ ringKrullDim R`. -/
theorem ringKrullDim_localization_le (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  refine Monotone.strictMono_of_injective ?_ (PrimeSpectrum.localization_comap_injective S M)
  intro a b hab
  exact Ideal.comap_mono hab

/-- Non-vacuity witness: the fraction field `ℚ` of `ℤ` (a localization at the non-zero-divisors) has
Krull dimension `0 ≤ 1 = ringKrullDim ℤ`. -/
example : ringKrullDim (Localization (nonZeroDivisors ℤ)) ≤ ringKrullDim ℤ :=
  ringKrullDim_localization_le (nonZeroDivisors ℤ) (Localization (nonZeroDivisors ℤ))

end DLNFibre.Core.Dimension
