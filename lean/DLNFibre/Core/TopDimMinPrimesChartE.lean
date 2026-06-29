/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.MinimalPrime.TopDimensional
import DLNFibre.Core.ChartLocalizedAlgEquiv
import DLNFibre.Core.ChartLocalizedCoordinates

/-!
# `DLNFibre.Core.TopDimMinPrimesChartE` — the chart `e` count wire

The middle rung of the fibre-`θ` count transport (expedition `theta-components`, thread 08): the
localized chart `AlgEquiv` `e : Localization.Away dsig ≃ₐ[k] Localization.Away gF`
(`Core.ChartLocalizedAlgEquiv.chartLocalizedAlgEquiv`) is a ring isomorphism, so it carries the
top-dimensional minimal-prime count across (`Ideal.topDimMinPrimes_ncard_eq_of_ringEquiv`, see
`Core.MinimalPrime.TopDimensional`):

> **`ncard_topDimMinPrimes_chartE_eq`** — `(TopDimMinPrimes (O(Σ^r)[1/dsig])).ncard =
> (TopDimMinPrimes ((O(F)[SchurVar])[1/gF])).ncard`.

This is the chart-`e`-ring-equiv arrow of the count chain (W1-localization → **chart e** →
W2-localization). The wire is mechanical — the iso is the LANDED route-β `chartLocalizedAlgEquiv`.

**Instance note.** The codomain ring `(O(F)[SchurVar])[1/gF]` is a localization of a polynomial ring
over a quotient ring — a *doubly-nested* `CommRing` whose instance synthesis overruns the default
search budget. The statement pins the ambient `CommRing` via `letI := inferInstance` so the
top-dimensional-minimal-prime set on the codomain elaborates; the proof rebinds the same instance.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Ideal (TopDimMinPrimes mem_topDimMinPrimes isPrime_of_mem_topDimMinPrimes
  comap_mem_topDimMinPrimes bijOn_comap_topDimMinPrimes topDimMinPrimes_ncard_eq_of_ringEquiv)

open MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The chart `e` carries the top-dimensional minimal-prime count.** The localized chart
`AlgEquiv` `chartLocalizedAlgEquiv` is a ring iso `O(Σ^r)[1/dsig] ≃ (O(F)[SchurVar])[1/gF]`, so
`topDimMinPrimes_ncard_eq_of_ringEquiv` transports the count. The chart-`e` arrow of the fibre-`θ`
count chain. -/
theorem ncard_topDimMinPrimes_chartE_eq [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    letI : CommRing (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
      (sweepFibreRing k d r hp hq)) := inferInstance
    (TopDimMinPrimes (Localization.Away (chartDsig k d r hp hq))).ncard
      = (TopDimMinPrimes (Localization.Away (chartGfib k d r hp hq))).ncard := by
  letI : CommRing (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
    (sweepFibreRing k d r hp hq)) := inferInstance
  exact topDimMinPrimes_ncard_eq_of_ringEquiv (chartLocalizedAlgEquiv k d r hp hq).toRingEquiv

end DLNFibre.Core
