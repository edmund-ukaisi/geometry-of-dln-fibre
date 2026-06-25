import DLNFibre.Core.FibreHeightDirect
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.FibreNormalForm

/-!
# `DLNFibre.Core.FibreCodimMinPrimes` — the H5 per-component → fibre-codimension closer

The **route-B assembly closer** (the non-redundant complement of thread 27's Jacobian-rank
certificate): turn *per-component height bounds* on the fibre `mult⁻¹(B)` into the fibre codimension.
`codimRepCanonical (fibre d B) = Ideal.height (fibreGenIdeal d B)` (H1, radical-insensitive), and
`Ideal.height I = ⨅_{J ∈ I.minimalPrimes} J.primeHeight` (the min over irreducible components), so the
codimension collapses to a value `v` once every component has `height ≥ v` and one (the top component)
has `height ≤ v`.

The inputs are carried as **explicit named hypotheses** (the conditional-bank pattern, as
`FibreReducedTrivialization` did for its `e`):

* `hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height` — every component has codim `≥ v`;
* `hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v` — one (top) component has codim `≤ v`.

With `v = C + δ = (cCodim d r).toNat + r(d_N + d_0 − r)`
(`codimRepCanonical_fibre_eq_cCodim_add_shift_of_height_bounds`),
this is the Lemma-4.6 fibre codimension. When the route-B tide (off thread 27's certificate) supplies
`rank(fibreJacobian) ≥ C+δ` generically on every component, those hypotheses discharge — via
`FibreJacobian` H3a (`finrank ker + rank = card`) + generic smoothness
(`SmoothLocalRelativeDimension`) + the catenary `height P + dim(R⧸P) = card` — and the full identity
`codim = C+δ` closes with **no re-work here**. Nothing in this module claims `hge`/`hle`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The interface-agnostic min-over-components closer -/

/-- **The min-over-components closer.** For any ideal `I` of a commutative ring whose minimal primes
all have `height ≥ v`, with one minimal prime of `height ≤ v`, the height is exactly `v`:
`Ideal.height I = ⨅_{J ∈ minimalPrimes} primeHeight J` collapses to `v`. Pure `ℕ∞` lattice reasoning.
(Stated with `Ideal.height` on the minimal primes — `= primeHeight` for a prime, but `height` avoids
the `IsPrime`-instance plumbing inside the binder.) -/
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

/-! ## The fibre-codimension closer (H1-wired) -/

/-- **The fibre-codimension closer (conditional).** For an algebraically closed field, given the
per-component height bounds on `fibreGenIdeal d B` — every minimal prime `height ≥ v`, one `≤ v` — the
fibre codimension is exactly `v`. Wires the LANDED H1 retarget (`codimRepCanonical (fibre d B) =
height (fibreGenIdeal d B)`) and the min-over-components closer. The route-B tide discharges `hge`/`hle`
from thread 27's Jacobian rank. -/
theorem codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds [IsAlgClosed k]
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (v : ℕ∞)
    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height)
    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v) :
    codimRepCanonical (fibre d B) = v := by
  rw [codimRepCanonical_fibre_eq_height_fibreGenIdeal]
  exact height_eq_of_minimalPrimes_bounds (fibreGenIdeal d B) v hge hle

/-! ## The Lemma-4.6 headline at `v = C + δ` -/

/-- **The Lemma-4.6 fibre codimension (conditional on the per-component height bounds).** For a rank-`r`
target `B` over an algebraically closed field, given that every minimal prime of `fibreGenIdeal d B`
has `height ≥ C + δ` and one has `height ≤ C + δ` (`C = cCodim d r`, `δ = r(d_N + d_0 − r)`), the fibre
codimension is `C + δ`. `codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds` at `v := C + δ`.
The route-B tide discharges the two hypotheses from thread 27's `rank(d mult) ≥ C+δ` (every component)
+ `= C+δ` (top component), via H3a + generic smoothness + the catenary. -/
theorem codimRepCanonical_fibre_eq_cCodim_add_shift_of_height_bounds [IsAlgClosed k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes,
      ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞) ≤ J.height)
    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes,
      J.height ≤ ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)) :
    codimRepCanonical (fibre d B)
      = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞) :=
  codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds d B _ hge hle

/-! ## G1 transport: the per-component bounds at ONE rank-`r` witness suffice

`Core.FibreNormalForm.codimRepCanonical_fibre_eq_of_rank_eq` (LANDED, flatness-free, via the GL×GL
endpoint action) makes the fibre codimension **constant over all rank-`r` targets**. So the route-B
tide need establish the per-component height bounds at only ONE tractable rank-`r` witness `B*`; G1
transports `codim(fibre B*) = codim(fibre B)` to every rank-`r` `B`. -/

/-- **G1-transported closer.** Over an infinite algebraically closed field with `N ≥ 1`, if the
per-component height bounds (every minimal prime `height ≥ v`, one `≤ v`) hold for the fibre over SOME
rank-`r` target `B*`, then **every** rank-`r` target `B` has `codimRepCanonical (fibre d B) = v`. The
closer gives `codim(fibre B*) = v`; G1 (`codimRepCanonical_fibre_eq_of_rank_eq`) transports it. -/
theorem codimRepCanonical_fibre_eq_of_rank_of_height_bounds_at_witness
    [IsAlgClosed k] [Infinite k] (d : Fin (N + 1) → ℕ) (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (Bstar B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ}
    (hBstar : Bstar.rank = r) (hB : B.rank = r) (v : ℕ∞)
    (hge : ∀ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, v ≤ J.height)
    (hle : ∃ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, J.height ≤ v) :
    codimRepCanonical (fibre d B) = v := by
  rw [codimRepCanonical_fibre_eq_of_rank_eq d hN B Bstar (by rw [hB, hBstar])]
  exact codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds d Bstar v hge hle

end DLNFibre.Core
