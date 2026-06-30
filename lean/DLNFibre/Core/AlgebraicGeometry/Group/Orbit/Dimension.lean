import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Basic
import DLNFibre.Core.Dimension.Localization
import DLNFibre.Core.Dimension.Codimension

/-!
# `DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Dimension` — the `varietyDim = trdeg` anchor (A4.1)

The squeeze's **lower anchor** on the abstract affine-`G`-variety carrier
`AlgebraicGeometry.Group.Orbit.AffineGVariety` (`Orbit/Basic.lean`). For an orbit-image variety
presented as the kernel/range of the coordinate pullback `μ* = aeval fρ`, its dimension is the
transcendence degree of the orbit coordinate algebra `k[fρ]`:

> `varietyDim Z = (trdeg k (μ*.range)).toNat`,  when `vanishingIdeal Z = ker μ*`.

This file holds the **abstract** A4.1 anchor; the DLN matrix-tuple specialisation
(`ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat`, `Core/AffineNoetherRank.lean`) re-derives
from it through the orbit↔kernel bridge `vanishingIdeal_range_orbitMap_eq_ker`.

## What enters where (name = content)

* `[Finite G.ρ]` is a hypothesis on these lemmas — NOT on the base carrier. It is the
  finite-generation input: with `G.ρ` finite the orbit coordinate algebra
  `G.pullback.range = Algebra.adjoin k (range G.fρ)` is a finitely-generated `k`-algebra, so the
  Phase-1 `dim = trdeg` fact (`ringKrullDim_eq_trdeg_of_fg_domain`) applies. The base carrier
  `Orbit/Basic.lean` deliberately keeps `ρ` finiteness off, so the irreducibility layer carries the
  minimal hypotheses; finiteness is added here, where dimension needs it.
* The **A0 bridge** `vanishingIdeal k Z = RingHom.ker G.pullback.toRingHom` is a hypothesis on
  `varietyDim_eq_trdeg_of_eq_ker`: the orbit↔kernel equality is a model-specific input that the
  concrete instance supplies (for the DLN matrix tuple, `vanishingIdeal_range_orbitMap_eq_ker`); the
  abstract carrier never asserts the orbit or its point set exists.

The transport is the first-iso `MvPolynomial G.ρ k ⧸ ker μ* ≃ₐ[k] μ*.range`
(`Ideal.quotientKerEquivRange`), carried through `ringKrullDim_eq_of_ringEquiv`. The orbit
coordinate algebra is a domain (subalgebra of the domain `G.R`), automatically.

The eventual Mathlib home is `Mathlib.AlgebraicGeometry.Group.Orbit.Dimension`; the namespace here
mirrors that target (bare `AlgebraicGeometry.Group.Orbit`) so the lift is a file-move.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace AlgebraicGeometry.Group.Orbit

open MvPolynomial DLNFibre.Core.Dimension

namespace AffineGVariety

universe u

variable {k : Type u} [Field k] (G : AffineGVariety k)

/-- The orbit coordinate algebra `G.pullback.range = k[fρ]` is a **finitely-generated** `k`-algebra
when the ambient coordinate index `G.ρ` is finite: it is the range of `μ* : MvPolynomial G.ρ k →ₐ[k]
G.R`, and `MvPolynomial G.ρ k` is finite-type over `k` for finite `G.ρ`. -/
instance finiteType_pullback_range [Finite G.ρ] : Algebra.FiniteType k G.pullback.range := by
  haveI : Fintype G.ρ := Fintype.ofFinite _
  exact Algebra.FiniteType.of_surjective G.pullback.rangeRestrict
    (AlgHom.rangeRestrict_surjective _)

/-- **Abstract A4.1 anchor (orbit-coordinate-algebra form).** For a finite ambient coordinate index
`G.ρ`, the Krull dimension of the orbit coordinate algebra `G.pullback.range = k[fρ]` equals its
transcendence degree over `k`:
`(ringKrullDim G.pullback.range).unbotD 0 = (Algebra.trdeg k G.pullback.range).toNat`.

`G.pullback.range` is a finitely-generated `k`-domain (`finiteType_pullback_range`; a subalgebra of
the domain `G.R`), so this is the Phase-1 f.g.-domain fact `ringKrullDim_eq_trdeg_of_fg_domain` read
off in `.unbotD`/`.toNat` form. Char-free. -/
theorem ringKrullDim_pullback_range_unbotD_eq_trdeg_toNat [Finite G.ρ] :
    (ringKrullDim G.pullback.range).unbotD 0
      = (Algebra.trdeg k G.pullback.range).toNat := by
  rw [ringKrullDim_eq_trdeg_of_fg_domain (k := k) G.pullback.range]
  exact WithBot.unbotD_coe 0 _

/-- **Abstract A4.1 anchor (variety-dimension form).** For a finite ambient coordinate index `G.ρ`
and a point set `Z ⊆ G.ρ → k` whose vanishing ideal *is* the pullback kernel — the **A0 bridge**
`vanishingIdeal k Z = ker μ*` that each concrete model supplies (for the DLN matrix tuple,
`vanishingIdeal_range_orbitMap_eq_ker`) — the variety dimension of `Z` equals the transcendence
degree of the orbit coordinate algebra `k[fρ]`:
`varietyDim Z = (Algebra.trdeg k G.pullback.range).toNat`.

The vanishing ideal is rewritten to `ker μ*` by the bridge; the coordinate ring
`MvPolynomial G.ρ k ⧸ ker μ*` is `k`-algebra isomorphic to `μ*.range` (first iso theorem
`Ideal.quotientKerEquivRange`), transporting the Krull dimension
(`ringKrullDim_eq_of_ringEquiv`); then the orbit-coordinate-algebra anchor closes it. Char-free; the
abstract carrier never asserts `Z` (or the orbit) exists — the bridge is the model input. -/
theorem varietyDim_eq_trdeg_of_eq_ker [Finite G.ρ] {Z : Set (G.ρ → k)}
    (hZ : MvPolynomial.vanishingIdeal k Z = RingHom.ker G.pullback.toRingHom) :
    varietyDim Z = ((Algebra.trdeg k G.pullback.range).toNat : ℕ∞) := by
  -- transport the coordinate ring through the first iso onto the orbit coordinate algebra
  let Ψ : (MvPolynomial G.ρ k ⧸ RingHom.ker G.pullback.toRingHom) ≃ₐ[k] G.pullback.range :=
    Ideal.quotientKerEquivRange G.pullback
  rw [varietyDim, hZ, ringKrullDim_eq_of_ringEquiv Ψ.toRingEquiv,
    ringKrullDim_eq_trdeg_of_fg_domain (k := k) G.pullback.range]
  exact WithBot.unbotD_coe 0 _

end AffineGVariety

end AlgebraicGeometry.Group.Orbit
