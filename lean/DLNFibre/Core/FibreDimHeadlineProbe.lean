import DLNFibre.Core.FibreDimFibration
import DLNFibre.Core.FibreDimEasyProbe
import DLNFibre.Core.FibreHeightDirect

/-!
# `DLNFibre.Core.FibreDimHeadlineProbe` — the pre-staged headline wiring (H5)

Un-aggregated probe: the final `codimRepCanonical (fibre E) = C+δ` headline, stated with thread 27's
per-component facts as **explicit hypotheses** (named, not `sorry`), proved by wiring the LANDED
engine bricks — the H1 retarget + the H5 min-over-components closer. Validates that the assembly
skeleton genuinely closes the headline given thread 27's input, so the final tide is a thin
substitution. Zero sorry.

The hypothesis interface here is the **height interface** on the minimal primes of `fibreGenIdeal`
(`primeHeight` of every component `≥ v`, one `≤ v`) — the cleanest feed to the H5 closer. The
`dim → height` conversion (from thread 27's component-dimension/Jacobian-rank facts, via the LANDED
catenary `height P + dim (R ⧸ P) = card`) is `ℕ∞` arithmetic the final tide runs once thread 27's
exact fact shape is fixed; it is engine-resident (`NullstellensatzCodim`), not staged here.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **Pre-staged headline wiring.** Given thread 27's per-component height facts on the minimal primes
of `fibreGenIdeal d E` — every component `height ≥ v`, one component `height ≤ v` — the fibre
codimension is exactly `v`. Wires the LANDED H1 retarget (`codim(fibre) = height(fibreGenIdeal)`) and
the H5 min-over-components closer (`height_eq_of_minimalPrimes_bounds`). With `v = C + δ` (thread 27's
value), this is the headline `codimRepCanonical (fibre E) = C + δ`. The hypotheses `hge`/`hle` are
exactly what generic smoothness + the catenary supply per component. -/
theorem codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds [IsAlgClosed k]
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (v : ℕ∞)
    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height)
    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v) :
    codimRepCanonical (fibre d B) = v := by
  rw [codimRepCanonical_fibre_eq_height_fibreGenIdeal]
  exact height_eq_of_minimalPrimes_bounds (fibreGenIdeal d B) v hge hle

end DLNFibre.Core
