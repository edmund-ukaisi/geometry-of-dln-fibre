import DLNFibre.Core.DeepChartRing
import DLNFibre.Core.AffineDomainDimension
import DLNFibre.Core.FibreDimFibration

/-!
# `DLNFibre.Core.FibreDimEasyProbe` — probe for the easy direction + the H5 closer

Un-aggregated probe pinning the descended-comorphism + the interface-agnostic min-over-components
closer (H5) the per-component height facts (from the Jacobian-rank route, thread 27) feed. Zero sorry.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The descended base→total algebra map `O(Mat^{≤r}) →ₐ[k] O(Σ̄^r)` -/

/-- The descended comorphism `(O(stratum) ⧸ sigmaIdeal_stratum) →ₐ[k] (O(Rep_d) ⧸ sigmaIdeal_d)`,
`deepBaseComap` lifted to the quotients via `deepBaseComap_sigmaIdeal_le`. -/
noncomputable def sigmaQuotComap (d : Fin (N + 1) → ℕ) (r : ℕ) :
    (MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k
        ⧸ sigmaIdeal (k := k) (dStratum (d 0) (d (Fin.last N))) r)
      →ₐ[k] (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r) :=
  Ideal.quotientMapₐ (sigmaIdeal (k := k) d r) (deepBaseComap (k := k) d)
    (Ideal.map_le_iff_le_comap.mp (deepBaseComap_sigmaIdeal_le d r))

/-! ## The H5 closer (interface-agnostic): `height I = v` from per-minimal-prime bounds

The per-component → codimension assembly. `Ideal.height I = ⨅_{J ∈ minimalPrimes} primeHeight J`, so
once the Jacobian-rank route (thread 27) supplies, for `I = fibreGenIdeal d E`:
* a uniform lower bound `primeHeight J ≥ v` for every minimal prime `J` (every component codim ≥ v),
* one witnessing minimal prime `J₀` with `primeHeight J₀ ≤ v` (the top component codim ≤ v),
the infimum collapses to `v`. Pure lattice reasoning over `ℕ∞`. -/

/-- **The min-over-components closer.** For any ideal `I` of a commutative ring whose minimal primes
all have `height ≥ v`, with one minimal prime of `height ≤ v`, the height is exactly `v`.
This is the H5 assembly that turns the per-component Jacobian-rank facts into `codim = C+δ`. (Stated
with `Ideal.height` on the minimal primes — `= primeHeight` for a prime, but `height` dodges the
`IsPrime`-instance plumbing inside the binder.) -/
theorem height_eq_of_minimalPrimes_bounds {R : Type*} [CommRing R] (I : Ideal R) (v : ℕ∞)
    (hge : ∀ J ∈ I.minimalPrimes, v ≤ J.height)
    (hle : ∃ J ∈ I.minimalPrimes, J.height ≤ v) :
    I.height = v := by
  apply le_antisymm
  · obtain ⟨J, hJ, hJle⟩ := hle
    exact le_trans (Ideal.height_mono hJ.1.2) hJle
  · rw [Ideal.height]
    refine le_iInf₂ fun J hJ ↦ ?_
    haveI := Ideal.minimalPrimes_isPrime hJ
    rw [← Ideal.height_eq_primeHeight]
    exact hge J hJ

end DLNFibre.Core
