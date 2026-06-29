import DLNFibre.Core.Dimension.Localization
import DLNFibre.Core.VarietyDimPolyExtension

/-!
# `DLNFibre.Core.ChartLocalizedPolyDim` — localized poly-extension dimension wrapper

The **dimension-arithmetic half** of the route-(c) step-3 chart trivialization (thread 31, the
"ROUTE-3" packaging: localize both sides, no-drop twice). It separates the mechanical Krull-dim
bookkeeping from the hard *localized chart `AlgEquiv`* and the two *avoidance certificates*, all of
which enter as named hypotheses.

Geometry. The chart `Σ^r ∩ U_Δ` is a free polynomial extension of the fibre ring only **after**
inverting `detΔ` (the variable gauge `chartGauge` involves `Δ⁻¹`), so the natural iso is the
localized `O(Σ^r)[1/detΔ] ≃ₐ[k] (MvPolynomial SchurVar O(F))[1/gF]`. Inverting `detΔ` on the source
and `gF` on the polynomial extension each does **not** drop the top dimension — each avoids a
top-dimensional minimal prime (`detΔ` by the pp-nodrop density cert; `gF` because it has a unit
`k`-coefficient, nonzero in every component). The shared affine-domain no-drop
`ringKrullDim_localizationAway_eq_of_avoids_top_prime` discharges both. With the two
localized dims equal to the un-localized ones, and the domain-free
`MvPolynomial.ringKrullDim_of_isNoetherianRing` giving the `+δ`, the chart identity
`dim O(Σ^r) = dim O(F) + δ` follows.

## Main results
- `ringKrullDim_eq_of_localized_polyExtensionAlgEquiv` — the `ringKrullDim` form.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- **The localized poly-extension Krull-dimension wrapper (ROUTE-3).** Suppose:
- `Osig` is the (un-localized) chart-closure coordinate ring and `Ofib` the fibre coordinate ring
  (both finite-type `k`-algebras, possibly reducible);
- `P = MvPolynomial ι Ofib` the free `δ`-variable extension (`ι` finite);
- `dsig : Osig` and `gfib : P` are the localizing elements;
- `e : Localization.Away dsig ≃ₐ[k] Localization.Away gfib` is the localized chart `AlgEquiv`;
- `hsig` / `hP` are the two no-drop equalities (`dim (Osig[1/dsig]) = dim Osig`,
  `dim (P[1/gfib]) = dim P`), each from
  `ringKrullDim_localizationAway_eq_of_avoids_top_prime` at its avoidance cert.

Then `ringKrullDim Osig = ringKrullDim Ofib + card ι`. Pure dimension arithmetic: transport across
`e`, the two no-drops, and `MvPolynomial.ringKrullDim_of_isNoetherianRing` (domain-free). -/
theorem ringKrullDim_eq_of_localized_polyExtensionAlgEquiv {ι : Type*} [Finite ι]
    (Osig : Type u) [CommRing Osig] [Algebra k Osig]
    (Ofib : Type u) [CommRing Ofib] [Algebra k Ofib] [IsNoetherianRing Ofib]
    (dsig : Osig) (gfib : MvPolynomial ι Ofib)
    (e : Localization.Away dsig ≃ₐ[k] Localization.Away gfib)
    (hsig : ringKrullDim (Localization.Away dsig) = ringKrullDim Osig)
    (hP : ringKrullDim (Localization.Away gfib) = ringKrullDim (MvPolynomial ι Ofib)) :
    ringKrullDim Osig = ringKrullDim Ofib + (Nat.card ι : ℕ∞) := by
  rw [← hsig, ringKrullDim_eq_of_ringEquiv e.toRingEquiv, hP,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
  norm_cast

end DLNFibre.Core
