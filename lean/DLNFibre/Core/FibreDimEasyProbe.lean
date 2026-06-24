import DLNFibre.Core.DeepChartRing
import DLNFibre.Core.AffineDomainDimension
import DLNFibre.Core.FibreDimFibration

/-!
# `DLNFibre.Core.FibreDimEasyProbe` — probe for the easy direction `codim(fibre E) ≤ C+δ`

Un-aggregated probe pinning the descended-comorphism + catenary scaffolding for the flatness-free
upper bound. Zero sorry.
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

end DLNFibre.Core
