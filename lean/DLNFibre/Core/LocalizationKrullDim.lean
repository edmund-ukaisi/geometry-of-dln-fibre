/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# `DLNFibre.Core.LocalizationKrullDim` — Krull dimension under localization (route-(c) rung-4 brick)

The localization-side dimension bricks for the route-(c) one-chart no-drop (thread 31 rung 4). A
localization `S = M⁻¹R` has `ringKrullDim S ≤ ringKrullDim R`: prime ideals of `S` correspond
(order-isomorphically) to primes of `R` disjoint from `M` (`IsLocalization.orderIsoOfPrime`), so
`comap (algebraMap R S)` is a strict-monotone injection of spectra, and Krull dimension is monotone
under strict-monotone maps (`Order.krullDim_le_of_strictMono`).

The matching `≥` (the genuine **no-drop**: inverting an element that avoids a top-dimensional minimal
prime does not drop the dimension) is the harder direction and lives in a downstream module; this
brick is the always-true `≤` half, reusable and domain-free.

## Main results
- `ringKrullDim_localization_le` — `ringKrullDim S ≤ ringKrullDim R` for any localization `S = M⁻¹R`.
-/

namespace DLNFibre.Core

open IsLocalization

universe u

variable {R : Type u} [CommRing R]

/-- **Localization does not increase Krull dimension.** For a localization `S = M⁻¹R`, the prime
spectrum of `S` order-embeds into that of `R` via `comap (algebraMap R S)` (the `IsLocalization`
prime correspondence `orderIsoOfPrime` is an order iso onto the `M`-disjoint primes, hence the
`comap` is strict-monotone). Krull dimension is monotone under strict-monotone maps, so
`ringKrullDim S ≤ ringKrullDim R`. -/
theorem ringKrullDim_localization_le (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R := by
  -- `PrimeSpectrum.comap (algebraMap R S)` is monotone (`comap` of a ring hom) and injective for a
  -- localization (`localization_comap_injective`), hence strict-monotone; Krull dim is monotone.
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  refine Monotone.strictMono_of_injective ?_ (PrimeSpectrum.localization_comap_injective S M)
  intro a b hab
  exact Ideal.comap_mono hab

end DLNFibre.Core

/-- Non-vacuity witness: the fraction field `ℚ` of `ℤ` (a localization at `ℤ \ {0}`) has Krull
dimension `0 ≤ 1 = ringKrullDim ℤ`. -/
example : ringKrullDim (Localization (nonZeroDivisors ℤ)) ≤ ringKrullDim ℤ :=
  DLNFibre.Core.ringKrullDim_localization_le (nonZeroDivisors ℤ) (Localization (nonZeroDivisors ℤ))

