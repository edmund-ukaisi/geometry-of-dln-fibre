import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Basic` — abstract affine `G`-variety carrier

The reusable, network-free carrier behind the orbit-dimension argument. An orbit `G · M` in an
affine space `𝔸^ρ` is presented as the image of an irreducible algebraic group `G` under a
polynomial orbit map; its coordinate data is captured by the **pullback** `aeval fρ`, the
`k`-algebra hom `MvPolynomial ρ k →ₐ[k] R` sending the `x`-th ambient coordinate to the
orbit-coordinate family member `fρ x ∈ R`. Here `R = 𝒪(G)` is the (irreducible, hence
integral-domain) coordinate ring of the group, so `fρ x` is the generic orbit coordinate as an
element of `𝒪(G)`.

This file is the **base layer** of the Phase-2 de-`Tuple` refactor: it holds only the data and facts
that need *no* deformation/cotangent structure, namely

* the carrier `structure AffineGVariety` — `(ρ, R, fρ : ρ → R)` with `R` a `k`-domain;
* **orbit-as-image irreducibility** (`AffineGVariety.isPrime_ker_pullback` and equivalents): the
  pullback's kernel is a prime ideal, equivalently the Zariski closure of the orbit image is an
  irreducible variety. The single deep input is `R` being a domain; the matrix-tuple presentation is
  one instance.

The deformation data `(C0, C1, δ : C0 →ₗ[k] C1)` that the rank/cotangent bricks (P2.4/P2.5) consume
is added in a *separate later extension* (`AffineGVarietyDeformation`), so that this irreducibility
layer carries the **minimal** hypotheses. The eventual Mathlib home is
`Mathlib.AlgebraicGeometry.Group.Orbit.Basic`; the namespace here mirrors that target so the lift is
a file-move.

The DLN matrix-tuple is wired in as the first instance in
`DLNFibre.Core.OrbitVariety` (`Core/OrbitVariety.lean`): `DLNFibre.Core.dlnOrbit M` constructs the
carrier from `(RepCoord d, groupRing d, genericOrbitCoord M)`, and the DLN
`isPrime_vanishingIdeal_orbitSet` derives from the abstract fact through the orbit↔kernel bridge.
-/

namespace AlgebraicGeometry.Group.Orbit

open MvPolynomial

universe u

/-- **Abstract affine-`G`-variety carrier (orbit-as-image base layer).** The data needed to state
orbit-as-image irreducibility, with no deformation/cotangent structure (those are added in the
later `AffineGVarietyDeformation` extension, so this layer keeps the *minimal* hypotheses).

The DLN matrix-tuple is one instance (`ρ := RepCoord d`, `R := groupRing d`,
`fρ := genericOrbitCoord M`); the abstract facts below are properties of *this presentation* (an
`aeval` pullback into a domain), not consequences of a bare orbit map. -/
structure AffineGVariety (k : Type u) [Field k] where
  /-- The ambient affine-space coordinate index — the `RepCoord d` analogue: one variable per
  coordinate of the representation space the orbit lives in. -/
  ρ : Type
  /-- The group coordinate ring `𝒪(G)`, an integral domain (the group `G` is irreducible). The
  `groupRing d = Localization.Away Δ` of the DLN instance is one model. -/
  R : Type u
  [commRing : CommRing R]
  [isDomain : IsDomain R]
  [algebra : Algebra k R]
  /-- The orbit-coordinate family `fρ x = (μ_M^* X_x) ∈ 𝒪(G)`: the `x`-th ambient coordinate of the
  generic orbit point, as an element of the group coordinate ring. The DLN instance uses
  `genericOrbitCoord M`. -/
  fρ : ρ → R

namespace AffineGVariety

variable {k : Type u} [Field k] (G : AffineGVariety k)

attribute [instance] AffineGVariety.commRing AffineGVariety.isDomain AffineGVariety.algebra

/-- The **orbit-map pullback** `μ_M^* : MvPolynomial G.ρ k →ₐ[k] G.R`, the `k`-algebra hom sending
the ambient coordinate variable `X x` to the orbit-coordinate family member `G.fρ x`. The matrix
tuple's `orbitPullback M` is this `aeval` for the instance `fρ = genericOrbitCoord M`. -/
noncomputable def pullback : MvPolynomial G.ρ k →ₐ[k] G.R :=
  MvPolynomial.aeval G.fρ

@[simp] theorem pullback_X (x : G.ρ) : G.pullback (MvPolynomial.X x) = G.fρ x :=
  MvPolynomial.aeval_X _ _

/-- The pullback's range is the **orbit coordinate algebra** `k[fρ x] = Algebra.adjoin k (range fρ)`
inside the domain `G.R`. This is the coordinate ring of the orbit-image's Zariski closure. -/
theorem range_pullback :
    G.pullback.range = Algebra.adjoin k (Set.range G.fρ) := by
  rw [pullback, MvPolynomial.aeval_range]

/-! ## Orbit-as-image irreducibility

The single primitive: the pullback kernel is prime, because it is a kernel into the domain `G.R`.
Every equivalent reading (the orbit coordinate algebra is a domain; the presentation ideal of the
orbit-image-closure is prime) is a one-step transport of this. -/

/-- **Orbit-as-image irreducibility (kernel primitive).** The kernel of the pullback
`μ_M^* = aeval fρ` is a **prime** ideal of `MvPolynomial G.ρ k`: it is a kernel into the domain
`G.R`, so the presentation algebra `MvPolynomial ρ k ⧸ ker` is a subalgebra of `G.R`, hence itself a
domain. The only input is `G.R` being a domain (`RingHom.ker_isPrime`); `G.fρ` and the `aeval` shape
are otherwise free. When `G.fρ` is the coordinate pullback of an orbit map (as in the DLN instance),
this primeness is read geometrically as irreducibility of the Zariski closure of the orbit image. -/
theorem isPrime_ker_pullback :
    (RingHom.ker G.pullback.toRingHom).IsPrime :=
  RingHom.ker_isPrime G.pullback.toRingHom

/-- **Orbit-as-image irreducibility (quotient-is-domain reading).** The presentation algebra of the
orbit-image closure, `MvPolynomial G.ρ k ⧸ ker μ_M^*`, is an integral domain — the coordinate-ring
form of "the closure is irreducible". A direct transport of `isPrime_ker_pullback`. -/
theorem isDomain_quotient_ker_pullback :
    IsDomain (MvPolynomial G.ρ k ⧸ RingHom.ker G.pullback.toRingHom) :=
  haveI := G.isPrime_ker_pullback
  inferInstance

/-- **Orbit-as-image irreducibility (vanishing-ideal form).** Given a point set `Z ⊆ ρ → k` whose
vanishing ideal *is* the pullback kernel — the orbit↔kernel bridge that each concrete model supplies
(for the matrix tuple, `vanishingIdeal_range_orbitMap_eq_ker`) — that vanishing ideal is prime, i.e.
`Z` is Zariski-irreducible. This is the form the geometric consumers want; the bridge hypothesis is
the only model-specific input. -/
theorem isPrime_vanishingIdeal_of_eq_ker {Z : Set (G.ρ → k)}
    (hZ : MvPolynomial.vanishingIdeal k Z = RingHom.ker G.pullback.toRingHom) :
    (MvPolynomial.vanishingIdeal k Z).IsPrime := by
  rw [hZ]; exact G.isPrime_ker_pullback

end AffineGVariety

end AlgebraicGeometry.Group.Orbit
