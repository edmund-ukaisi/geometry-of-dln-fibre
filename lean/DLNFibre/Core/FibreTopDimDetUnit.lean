/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreDetUnit
import DLNFibre.Core.MinimalPrime.TopDimensional

/-!
# `DLNFibre.Core.FibreTopDimDetUnit` — inverting `detΔ` keeps the fibre's `TopDimMinPrimes` count

The fibre-side endpoint of the chart count transport (expedition `theta-components`, thread 06).
The deep pivot minor `detΔ = ΔPdeep d r` is a **unit** on the fibre coordinate ring
`O(fibre) = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E` (`Core.FibreDetUnit`,
`fibreLocalizationAwayDetΔ_algEquiv`), so inverting it is an algebra isomorphism — and a ring
isomorphism preserves the top-dimensional minimal-prime count (`Core.TopDimMinPrimes`,
`topDimMinPrimes_ncard_eq_of_ringEquiv`). So passing to the pivot chart `{detΔ ≠ 0}` is invisible on
the fibre's component count:

> **`ncard_topDimMinPrimes_fibre_eq_localization`** — `(TopDimMinPrimes (O(fibre))).ncard =
> (TopDimMinPrimes (O(fibre)[1/detΔ])).ncard`.

This is the reducedness-free Route-A kill-condition (thread 04) at the level of the *count*: the
fibre's top-component count survives the localization the chart `e` requires, unconditionally.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Ideal (TopDimMinPrimes mem_topDimMinPrimes isPrime_of_mem_topDimMinPrimes
  comap_mem_topDimMinPrimes bijOn_comap_topDimMinPrimes topDimMinPrimes_ncard_eq_of_ringEquiv)

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **Inverting `detΔ` preserves the fibre's top-dimensional minimal-prime count.** Since `detΔ` is
a unit on `O(fibre)` (`Core.FibreDetUnit`), `fibreLocalizationAwayDetΔ_algEquiv` is a ring
isomorphism `O(fibre) ≃ O(fibre)[1/detΔ]`, and `topDimMinPrimes_ncard_eq_of_ringEquiv` carries the
count across. The fibre-side count endpoint of the chart transport — no reducedness, any `d`, any
`r ≤ d last`, `r ≤ d 0`, any field. -/
theorem ncard_topDimMinPrimes_fibre_eq_localization (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k
        ⧸ fibreGenIdeal d (normalForm (k := k) (d (Fin.last N)) (d 0) r hp hq))).ncard
      = (TopDimMinPrimes (Localization.Away (Ideal.Quotient.mk
          (fibreGenIdeal d (normalForm (k := k) (d (Fin.last N)) (d 0) r hp hq))
          (ΔPdeep d r hp hq)))).ncard :=
  topDimMinPrimes_ncard_eq_of_ringEquiv
    (fibreLocalizationAwayDetΔ_algEquiv d r hp hq).toRingEquiv

end DLNFibre.Core
