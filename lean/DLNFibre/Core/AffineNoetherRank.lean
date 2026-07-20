import DLNFibre.Core.OrbitPullbackDim
import DLNFibre.Core.PolynomialDimension
import DLNFibre.Core.Dimension.Localization
import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Dimension

/-!
# `DLNFibre.Core.AffineNoetherRank` — A4.1: `ringKrullDim = trdeg` for the pullback image

Route-c second link: for the finitely-generated `k`-domain `Aimg = (orbitPullback M).range`,
its Krull dimension equals its transcendence degree over `k`:

> `(ringKrullDim (orbitPullback M).range).unbotD 0`
> ` = (Algebra.trdeg k (orbitPullback M).range).toNat`.

This is the **orbit specialisation** of the abstract A4.1 anchor on the affine-`G`-variety carrier
(`AffineGVariety.ringKrullDim_pullback_range_unbotD_eq_trdeg_toNat`,
`Core/AlgebraicGeometry/Group/Orbit/Dimension.lean`). The abstract anchor reads `dim = trdeg` off
the f.g. `k`-domain `μ*.range` (the Phase-1 `Dimension.ringKrullDim_eq_trdeg_of_fg_domain`,
where `[Finite ρ]` is the finite-generation input). The DLN instance `dlnOrbit M`
(`Core/OrbitVariety.lean`) has `(dlnOrbit M).pullback = orbitPullback M` definitionally, so the
specialisation is the anchor at `dlnOrbit M` transported by `dlnOrbit_pullback`.

Char-free: no algebraic closure, no `CharZero` (the dimension engine and `trdeg` API are char-free).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Algebra DLNFibre.Core.Dimension AlgebraicGeometry.Group.Orbit

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Transport to the orbit-pullback image -/

/-- **A4.1 headline.** For the pullback image `Aimg = (orbitPullback M).range`, a finitely-generated
`k`-domain, the Krull dimension equals the transcendence degree:
`(ringKrullDim (orbitPullback M).range).unbotD 0 = (Algebra.trdeg k (orbitPullback M).range).toNat`.
The orbit specialisation of the abstract carrier anchor
`AffineGVariety.ringKrullDim_pullback_range_unbotD_eq_trdeg_toNat`: the DLN instance `dlnOrbit M`
satisfies `(dlnOrbit M).pullback = orbitPullback M` (`dlnOrbit_pullback`, definitional), and
`(dlnOrbit M).ρ = RepCoord d` is `Finite`, so the anchor applies and transports back. Char-free. -/
theorem ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    (ringKrullDim (orbitPullback M).range).unbotD 0
      = (Algebra.trdeg k (orbitPullback M).range).toNat := by
  haveI : Finite (dlnOrbit M).ρ := inferInstanceAs (Finite (RepCoord d))
  have h := (dlnOrbit M).ringKrullDim_pullback_range_unbotD_eq_trdeg_toNat
  rwa [dlnOrbit_pullback] at h

end DLNFibre.Core
