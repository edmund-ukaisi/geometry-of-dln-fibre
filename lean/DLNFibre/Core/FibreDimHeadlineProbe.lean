import DLNFibre.Core.FibreDimFibration
import DLNFibre.Core.FibreDimEasyProbe
import DLNFibre.Core.FibreHeightDirect
import DLNFibre.Core.FibreNormalForm

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

/-! ## G1-transported headline: the per-component bound at ONE rank-r point suffices

`Core.FibreNormalForm.codimRepCanonical_fibre_eq_of_rank_eq` (LANDED, flatness-free, via the GL×GL
endpoint action) makes the fibre codimension **constant over all rank-`r` targets**. So thread 27 need
prove the per-component height bounds at only ONE tractable rank-`r` point `B*` (e.g. the normal form
`E`, or whichever fibre is cleanest); G1 then transports `codim(fibre B*) = codim(fibre B)` to every
rank-`r` `B`. This is the "no-jump" — already proved, not via flatness. -/

/-- **G1-transported headline.** Over an infinite algebraically closed field with `N ≥ 1`, if the
per-component height bounds (every minimal prime `height ≥ v`, one `≤ v`) hold for the fibre over SOME
rank-`r` target `B*`, then **every** rank-`r` target `B` has `codimRepCanonical (fibre d B) = v`. The
H5 closer gives `codim(fibre B*) = v`; G1 (`codimRepCanonical_fibre_eq_of_rank_eq`) transports it.
Thread 27 supplies the bounds at one tractable `B*`; this delivers the value at all rank-`r` `B`. -/
theorem codimRepCanonical_fibre_eq_of_rank_of_height_bounds_at_witness
    [IsAlgClosed k] [Infinite k] (d : Fin (N + 1) → ℕ) (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (Bstar B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ}
    (hBstar : Bstar.rank = r) (hB : B.rank = r) (v : ℕ∞)
    (hge : ∀ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, v ≤ J.height)
    (hle : ∃ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, J.height ≤ v) :
    codimRepCanonical (fibre d B) = v := by
  have hstar : codimRepCanonical (fibre d Bstar) = v :=
    codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds d Bstar v hge hle
  rw [codimRepCanonical_fibre_eq_of_rank_eq d hN B Bstar (by rw [hB, hBstar])]
  exact hstar

end DLNFibre.Core
