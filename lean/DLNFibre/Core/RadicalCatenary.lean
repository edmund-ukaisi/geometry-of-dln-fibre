import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.Dimension.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `DLNFibre.Core.RadicalCatenary` — the reducible-locus catenary at the geometry layer

The any-proper-ideal catenary for a polynomial ring `R = MvPolynomial σ k` (`σ` finite, `k` any
field),

> `height I + ringKrullDim (R ⧸ I) = Nat.card σ`   (any `I ≠ ⊤`, no primality, no radicality),

now lives in `DLNFibre.Core.Dimension.Codimension` as
`height_add_ringKrullDim_quotient_eq_card_of_ne_top` — the network-free, closure-free dimension fact,
alongside the prime form `height_add_ringKrullDim_quotient_eq_card` (its special case). This file
carries only the **`Tuple`-coupled DLN specialisation**: the headline specialises to
`codimRepCanonical Z + varietyDim Z = card` for any **nonempty** Zariski-closed `Z` (over any field
its vanishing ideal is radical — `vanishingIdeal_isRadical`; nonempty makes it proper —
`vanishingIdeal_ne_top_of_nonempty`), discharging the reducible-locus catenary that
`Core.RouteCAssembly` carries as the named hypotheses `hCatFibre`/`hCatSigma`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open MvPolynomial Ideal Order

namespace DLNFibre.Core

open Dimension

universe u

variable {k : Type u} [Field k] {σ : Type*}

/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`)

The any-proper-ideal catenary itself (`height_add_ringKrullDim_quotient_eq_card_of_ne_top`, with its
two supporting bricks `exists_minimalPrime_height_eq_height`,
`exists_minimalPrime_ringKrullDim_quotient_ge`) now lives in `DLNFibre.Core.Dimension.Codimension`
alongside the prime form — it is the network-free dimension fact, with no closure import on its
path.
This file carries only the `Tuple`-coupled DLN specialisation below; the moved decls are reachable
unqualified here via `open Dimension`. -/

/-- The vanishing ideal of a **nonempty** set is proper: a polynomial vanishing on a point `x ∈ Z`
cannot be the unit `1` (which evaluates to `1 ≠ 0`), so `vanishingIdeal Z ≠ ⊤`. -/
theorem vanishingIdeal_ne_top_of_nonempty [Finite σ] {Z : Set (σ → k)} (hZ : Z.Nonempty) :
    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)) ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hZ
  rw [Ideal.ne_top_iff_one]
  intro hone
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hone
  have := hone x hx
  rw [map_one] at this
  exact one_ne_zero this

variable {N : ℕ}

/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
**nonempty** subset `Z ⊆ Rep_d` whose canonical flattening `canonicalCoord d '' Z` is Zariski-closed
(its vanishing ideal is radical and proper), the geometric codimension plus the variety dimension
equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
irreducibility hypothesis — the reducible-locus catenary converted to `ℕ∞` (the quotient is
nontrivial, so `ringKrullDim ≠ ⊥`). -/
theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
    {Z : Set (Tuple (k := k) d)} (hZ : (canonicalCoord d '' Z).Nonempty) :
    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
      = (Nat.card (RepCoord d) : ℕ∞) := by
  have hIne : (vanishingIdeal k (canonicalCoord d '' Z) :
      Ideal (MvPolynomial (RepCoord d) k)) ≠ ⊤ :=
    vanishingIdeal_ne_top_of_nonempty hZ
  have key := height_add_ringKrullDim_quotient_eq_card_of_ne_top
    (vanishingIdeal k (canonicalCoord d '' Z)) hIne
  haveI : Nontrivial (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) :=
    Ideal.Quotient.nontrivial_iff.mpr hIne
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim
      (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) :=
    ringKrullDim_nonneg_of_nontrivial
  have hne : ringKrullDim
      (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) ≠ ⊥ :=
    fun h ↦ by rw [h] at hnn; exact absurd hnn (by simp)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
  rw [← hm] at key
  exact_mod_cast key

/-! ## Non-vacuity witness

The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
(nonempty) of the `(2,2,2)` representation over `AlgebraicClosure ℚ`: `codim univ + dim univ =
card`, the concrete satisfiable instance with `codim univ = 0`, `dim univ = card`. -/
example :
    codimRepCanonical (Set.univ : Set (Tuple (k := AlgebraicClosure ℚ) dWitness))
      + varietyDim (canonicalCoord dWitness ''
          (Set.univ : Set (Tuple (k := AlgebraicClosure ℚ) dWitness)))
      = (Nat.card (RepCoord dWitness) : ℕ∞) :=
  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
    ((Set.univ_nonempty (α := Tuple (k := AlgebraicClosure ℚ) dWitness)).image _)

end DLNFibre.Core
