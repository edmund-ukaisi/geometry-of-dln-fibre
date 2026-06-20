import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.OrbitClosure
import DLNFibre.Core.NullstellensatzCodim

/-!
# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`

The first link of the L2b★ route-c chain that discharges `hVoigt` on the AG half. The variety
dimension of the determinantal rank locus `Z_M = canonicalCoord '' orbitRankLocus M` is identified
with the Krull dimension of the **image** of the orbit-map pullback `μ_M^*`, a finitely-generated
**domain** (subalgebra of the domain `𝒪(G_d) = groupRing d`).

Two moves, both char-free except for the algebraically-closed hypothesis the landed bricks force:

1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
   (`vanishingIdeal_orbitRankLocus_eq_orbitSet`), and the orbit↔kernel identity
   (`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`).
2. **First isomorphism theorem.** `(MvPolynomial (RepCoord d) k ⧸ ker μ_M^*) ≃ₐ[k] (μ_M^*).range`
   (`Ideal.quotientKerEquivRange`), so `ringKrullDim (… ⧸ ker μ_M^*) = ringKrullDim ((μ_M^*).range)`
   (`ringKrullDim_eq_of_ringEquiv`). The range is a subalgebra of the domain `groupRing d`
   (`groupRing_isDomain`), hence itself a domain.

The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
whose Krull dimension equals its transcendence degree; `isDomain_range_orbitPullback` records that
it is a domain.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- The orbit-map pullback's image `(μ_M^*).range` is a **domain**: a subalgebra of the domain
`𝒪(G_d) = groupRing d` (`groupRing_isDomain`). -/
instance isDomain_range_orbitPullback {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    IsDomain (orbitPullback M).range :=
  inferInstance

/-- **Route-c first link, ideal form.** The variety dimension of the rank locus `Z_M =
canonicalCoord '' orbitRankLocus M` equals the Krull dimension of the coordinate ring
`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
(`vanishingIdeal_orbitRankLocus_eq_orbitSet`) and the orbit↔kernel identity
(`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`) rewrite the vanishing ideal to
`ker μ_M^*`. -/
theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [IsAlgClosed k]
    {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    varietyDim (canonicalCoord d '' orbitRankLocus M)
      = (ringKrullDim (MvPolynomial (RepCoord d) k ⧸
          RingHom.ker (orbitPullback M).toRingHom)).unbotD 0 := by
  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
    vanishingIdeal_range_orbitMap_eq_ker M]

/-- The coordinate ring of `Z_M` is `k`-algebra isomorphic to the pullback image `(μ_M^*).range`:
the first isomorphism theorem `MvPolynomial (RepCoord d) k ⧸ ker μ_M^* ≃ₐ[k] (μ_M^*).range`. -/
noncomputable def quotientKerEquivRangeOrbitPullback {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    (MvPolynomial (RepCoord d) k ⧸ RingHom.ker (orbitPullback M).toRingHom)
      ≃ₐ[k] (orbitPullback M).range :=
  Ideal.quotientKerEquivRange (orbitPullback M)

/-- **Route-c first link, headline.** The variety dimension of the rank locus `Z_M =
canonicalCoord '' orbitRankLocus M` equals the Krull dimension of the pullback image `(μ_M^*).range`
— a finitely-generated **domain** (`isDomain_range_orbitPullback`), the object A4 computes as a
transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
first isomorphism theorem (`quotientKerEquivRangeOrbitPullback`) transported through
`ringKrullDim_eq_of_ringEquiv`. -/
theorem varietyDim_eq_ringKrullDim_range_orbitPullback [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    varietyDim (canonicalCoord d '' orbitRankLocus M)
      = (ringKrullDim (orbitPullback M).range).unbotD 0 := by
  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
    ringKrullDim_eq_of_ringEquiv (quotientKerEquivRangeOrbitPullback M).toRingEquiv]

section Witness

/-! ## Non-vacuity witness

The headline carries `[IsAlgClosed k]` (forced by the L1/L6.4 bricks), and `ℚ` is not algebraically
closed; the chain's objects, which do not need it, are exercised on the `(2,2,2)/ℚ` tuple
`tupleWitnessQ`. -/

/-- The pullback image `(μ_M^*).range` is a domain on the concrete `(2,2,2)/ℚ` tuple: the
`isDomain_range_orbitPullback` instance fires without algebraic closedness, the range objects being
non-vacuous on a real matrix tuple. -/
example : IsDomain (orbitPullback tupleWitnessQ).range :=
  isDomain_range_orbitPullback tupleWitnessQ

/-- The first isomorphism `MvPolynomial (RepCoord dWitness) ℚ ⧸ ker μ_M^* ≃ₐ[ℚ] (μ_M^*).range`
is inhabited on the concrete tuple (its source and target are the chain's ingredients). -/
noncomputable example :
    (MvPolynomial (RepCoord dWitness) ℚ ⧸ RingHom.ker (orbitPullback tupleWitnessQ).toRingHom)
      ≃ₐ[ℚ] (orbitPullback tupleWitnessQ).range :=
  quotientKerEquivRangeOrbitPullback tupleWitnessQ

end Witness

end DLNFibre.Core
