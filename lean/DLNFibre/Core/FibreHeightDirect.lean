import DLNFibre.Core.MultComorphism
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `DLNFibre.Core.FibreHeightDirect` — the radical-insensitive retarget of the fibre codimension (H1)

The first rung of the HEIGHT-DIRECT route to Lehalleur–Rimányi Lemma 4.6's geometry. The codimension
of the fibre `mult⁻¹(B)` is read as the `Ideal.height` of the vanishing ideal of its canonical
flattening (`Core.OrbitCodim.codimRepCanonical`). Over an algebraically closed field, the engine's
Nullstellensatz identifies that vanishing ideal with the **radical** of the explicit generator ideal
`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
rung is that **the height does not see the radical**: `(radical I).height = I.height`, because an
ideal and its radical have the same minimal primes (`Ideal.radical_minimalPrimes`), and
`Ideal.height` is the infimum of `primeHeight` over the minimal primes.

So `codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height` — **unconditionally** (no radicality
of `fibreGenIdeal` needed). This decouples the codimension from the scheme-structure / cut-ideal
radicality question (the thread-20 wall): the codimension, hence the RLCT payoff that consumes it,
never depends on whether `fibreGenIdeal` is its own radical.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

/-! ## Radical-insensitivity of height (generic) -/

/-- **The height of an ideal is the height of its radical.** An ideal `I` and `I.radical` have the
same minimal primes (`Ideal.radical_minimalPrimes`), and `Ideal.height` is the infimum of the prime
heights over the minimal primes, so the two infima coincide. No hypothesis on `I`. -/
theorem Ideal.height_radical {R : Type*} [CommRing R] (I : Ideal R) :
    I.radical.height = I.height := by
  simp only [Ideal.height, Ideal.radical_minimalPrimes]

/-! ## The fibre codimension retarget (H1) -/

variable {k : Type u} [Field k] {N : ℕ}

/-- **H1 — the radical-insensitive retarget.** Over an algebraically closed field, the canonical
geometric codimension of the fibre `mult⁻¹(B)` equals the `Ideal.height` of the explicit generator
ideal `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`. The chain:
`codimRepCanonical (fibre d B) = height (vanishingIdeal (canonicalCoord d '' fibre d B))`
(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
(`vanishingIdeal_image_fibre_eq_radical`, the Nullstellensatz); `(radical I).height = I.height`
(`Ideal.height_radical`). The codimension does **not** depend on whether `fibreGenIdeal` is
radical. -/
theorem codimRepCanonical_fibre_eq_height_fibreGenIdeal [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height := by
  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]

/-! ## Non-vacuity witness -/

section Witness

/-- The `(2,2,2)` retarget over `AlgebraicClosure ℚ`: the fibre codimension over a target `B` is the
height of the explicit fibre generator ideal — `codimRepCanonical_fibre_eq_height_fibreGenIdeal` is
a genuine equation between the two named quantities (non-vacuous). -/
example (B : Matrix (Fin (dWitness (Fin.last 2))) (Fin (dWitness 0)) (AlgebraicClosure ℚ)) :
    codimRepCanonical (fibre dWitness B) = (fibreGenIdeal dWitness B).height :=
  codimRepCanonical_fibre_eq_height_fibreGenIdeal dWitness B

end Witness

end DLNFibre.Core
