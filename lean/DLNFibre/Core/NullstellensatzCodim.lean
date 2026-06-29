import DLNFibre.Core.Dimension.Codimension
import DLNFibre.Core.OrbitCodim
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# `DLNFibre.Core.NullstellensatzCodim` — the algebraically-closed layer + the `codimRep` consumers

The **field-general** core of the point-space ↔ `PrimeSpectrum` codimension bridge — the Zariski
predicates, `vanishingIdeal_isRadical`, the finite-index catenary transport, `varietyDim`, and the
bridge headline `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` — now lives in
`DLNFibre.Core.Dimension.Codimension` (over `[Field k] [Finite σ]`, no algebraic-closedness). This
file carries the two pieces that genuinely use more:

1. **The algebraically-closed / non-vacuity layer.** Over `[IsAlgClosed k]`, a Zariski-closed `Z`
   with prime vanishing ideal is **nonempty**
   (`nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal`, weak Nullstellensatz from the strong
   one through `vanishingIdeal_zeroLocus_eq_radical`); over an
   infinite field the vanishing ideal of the **whole space** is `⊥` (`vanishingIdeal_univ_eq_bot`,
   `[Infinite k]` — its true need — via `MvPolynomial.funext`). These route through Mathlib's
   `zeroLocus ↔ radical`, which does **not** weaken to `[PerfectField]`; the closure use here is
   genuine.

2. **The DLN `codimRep` specialisations.** The bridge headline at the geometry layer's coordinatised
   consumer (`codimRep`, `codimRepCanonical` over `Tuple`/`RepCoord d`).

The field-general core's short names are re-`export`ed into `DLNFibre.Core` below, so existing
consumers that reference them unqualified (`varietyDim`, `IsZariskiClosed`, …) continue to resolve
against `DLNFibre.Core` without an `open Dimension`.

`[IsAlgClosed k]` is a **hypothesis**, not a citation. Everything is proved; nothing is `sorry`/
`axiom`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open MvPolynomial Ideal

namespace DLNFibre.Core

open Dimension

-- Re-export the field-general codimension-bridge core (now in `DLNFibre.Core.Dimension`) under the
-- short `DLNFibre.Core` namespace, so existing unqualified consumers keep resolving.
export Dimension (IsZariskiClosed IsZariskiIrreducible vanishingIdeal_isRadical
  isZariskiIrreducible_iff_isPrime_vanishingIdeal ringKrullDim_mvPolynomial_finite
  height_add_ringKrullDim_quotient_eq_card varietyDim height_vanishingIdeal_add_varietyDim_eq_card
  height_vanishingIdeal_eq_card_sub_varietyDim)

universe u

variable {k : Type u} [Field k] {σ : Type*}

/-! ## The algebraically-closed / non-vacuity layer -/

/-- **Closed + prime ⟹ nonempty (weak Nullstellensatz).** A Zariski-closed `Z` whose vanishing ideal
is prime (hence proper) is nonempty: if `Z = ∅` then `vanishingIdeal Z = ⊤`, but the strong
Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
contradicting primality. -/
theorem nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal [IsAlgClosed k] [Finite σ]
    {Z : Set (σ → k)} (hZ : IsZariskiClosed Z)
    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
    Z.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  have htop : vanishingIdeal k Z = ⊤ := by
    have h2 : zeroLocus k (vanishingIdeal k Z) = (∅ : Set (σ → k)) := hZ ▸ hempty
    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
      vanishingIdeal_zeroLocus_eq_radical (K := k) _
    rw [h2, vanishingIdeal_empty] at h3
    exact Ideal.radical_eq_top.mp h3.symm
  exact hp.ne_top htop

/-- The vanishing ideal of the **whole space** `⊤ ⊆ (σ → k)` is `⊥` over any **infinite** field
(`[Infinite k]` is the true need — `[IsAlgClosed k]` ⟹ `[Infinite k]`): a polynomial vanishing at
every point of `σ → k` is `0` (`MvPolynomial.funext` over an infinite integral domain). -/
theorem vanishingIdeal_univ_eq_bot [Infinite k] :
    (vanishingIdeal k (Set.univ : Set (σ → k)) : Ideal (MvPolynomial σ k)) = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [Ideal.mem_bot]
  refine MvPolynomial.funext (R := k) fun x ↦ ?_
  have hx := hp x (Set.mem_univ x)
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hp
  rw [map_zero, ← MvPolynomial.aeval_eq_eval]
  exact hp x (Set.mem_univ x)

/-- Non-vacuity witness for the bridge: at the **whole space** `Z = univ` of `σ → k` (`k`
alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
reads `0 + Nat.card σ = Nat.card σ` — a concrete satisfiable instance, the dimension term carrying
the equality. -/
example [IsAlgClosed k] [Finite σ] :
    (vanishingIdeal k (Set.univ : Set (σ → k)) : Ideal (MvPolynomial σ k)).height
      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
  haveI : (vanishingIdeal k (Set.univ : Set (σ → k)) :
      Ideal (MvPolynomial σ k)).IsPrime := by rw [vanishingIdeal_univ_eq_bot]; infer_instance
  exact height_vanishingIdeal_add_varietyDim_eq_card this

/-! ## Specialisation to `codimRep` (the geometry layer's consumer) -/

variable {N : ℕ}

/-- **The bridge at `codimRep` (additive).** For any coordinatisation `coord` and a subset `Z ⊆
Rep_d` whose image `coord '' Z` is an irreducible variety, the geometric codimension `codimRep coord
Z` plus the variety dimension of `coord '' Z` equals the ambient dimension `Nat.card (RepCoord d)`.
`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
theorem codimRep_add_varietyDim_eq_card {d : Fin (N + 1) → ℕ}
    (coord : Tuple (k := k) d ≃ (RepCoord d → k)) (Z : Set (Tuple (k := k) d))
    (hp : (vanishingIdeal k (coord '' Z) : Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
  height_vanishingIdeal_add_varietyDim_eq_card hp

/-- **The bridge at `codimRep` (subtraction).** `codimRep coord Z = Nat.card (RepCoord d) −
varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
`−` variety dimension. -/
theorem codimRep_eq_card_sub_varietyDim {d : Fin (N + 1) → ℕ}
    (coord : Tuple (k := k) d ≃ (RepCoord d → k)) (Z : Set (Tuple (k := k) d))
    (hp : (vanishingIdeal k (coord '' Z) : Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
  height_vanishingIdeal_eq_card_sub_varietyDim hp

/-- **The bridge at `codimRepCanonical` (subtraction).** At the canonical entry-flattening
`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
Z)` for an irreducible variety — the genuine geometric codimension. -/
theorem codimRepCanonical_eq_card_sub_varietyDim {d : Fin (N + 1) → ℕ}
    (Z : Set (Tuple (k := k) d))
    (hp : (vanishingIdeal k (canonicalCoord d '' Z) :
      Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp

end DLNFibre.Core
