/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartLocalizedCoordinates
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# `DLNFibre.Core.ChartAwayZero` — the schur-side away-localization zero-test (Ψ descent, seam B.0)

The target-side (schur-side) zero-test of the route-β Ψ descent (thread 31): the analog, for the
poly-over-quotient target `P = MvPolynomial SchurVar O(F)`, of the LANDED source-side clearing-
denominators primitive `away_eq_zero_iff_exists_pow_mul_mem`. Whereas the source side localizes a
`vanishingIdeal`-quotient ring, the schur side localizes `P` (a polynomial ring over a quotient), so
the zero-test is the GENERIC `IsLocalization.mk'_eq_zero_iff` on `P` directly (it holds over any base
ring), unwound at the away-submonoid `powers gF`:

> `algebraMap P (Localization.Away gF) a = 0 ↔ ∃ n, gF ^ n * a = 0`   (in `P`).

This is the gF-side bridge the Ψ descent rides: once a numerator `a : P` is shown to be killed by a
power of `gF` (the schur determinant with `O(F)` coefficients), its image in the localization is `0`.

## Main results
- `away_algebraMap_eq_zero_iff` — the generic away-localization zero-test on a poly-over-quotient ring.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The schur-side away-localization zero-test.** For any localizing element `g : R` of a
commutative ring `R` and its away-localization `Localization.Away g`, an element `a : R` maps to `0`
exactly when some power of `g` kills it: `algebraMap R (Away g) a = 0 ↔ ∃ n, g ^ n * a = 0`. The
generic `IsLocalization.mk'_eq_zero_iff` at the away-submonoid `powers g`, with the
`algebraMap = mk' · 1` identification. (Stated abstractly; instantiated at `R = P`, `g = gF`.) -/
theorem away_algebraMap_eq_zero_iff {R : Type u} [CommRing R] (g a : R) :
    algebraMap R (Localization.Away g) a = 0 ↔ ∃ n : ℕ, g ^ n * a = 0 := by
  rw [← IsLocalization.mk'_one (M := Submonoid.powers g) (Localization.Away g) a,
    IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨m, n, rfl⟩, hm⟩
    exact ⟨n, by simpa using hm⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨g ^ n, n, rfl⟩, by simpa using hn⟩

end DLNFibre.Core
