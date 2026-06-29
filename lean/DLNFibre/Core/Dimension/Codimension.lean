import DLNFibre.Core.Dimension.Catenary
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# `DLNFibre.Core.Dimension.Codimension` — the point-space ↔ `PrimeSpectrum` codimension bridge

For a finite coordinate index `σ` and an **arbitrary field** `k`, this file connects the
**geometric** codimension of a subset `Z ⊆ (σ → k)` — the `Ideal.height` of its vanishing ideal — to
the **variety dimension** of `Z` (the Krull dimension of its coordinate ring) via the catenary
identity for affine space. It is the field-general core of the codimension bridge; the
algebraically-closed geometric/non-vacuity layer (zero-locus ↔ radical, weak-Nullstellensatz
non-emptiness) lives in `DLNFibre.Core.NullstellensatzCodim`, and the DLN `codimRep` specialisations
live there too.

This file mirrors the eventual Mathlib home for the codimension of affine algebraic sets
(`Mathlib.AlgebraicGeometry.Codimension` once that lands), and builds on `Core.Dimension.Catenary`
(the polynomial-ring catenary equality `height_add_ringKrullDim_quotient_eq`, reused as a black
box — no catenary re-induction).

## Contents

1. **Zariski-closed / irreducible predicates** on the point space `σ → k`
   (`IsZariskiClosed`, `IsZariskiIrreducible`), and the algebraic translation of irreducibility:
   `IsZariskiIrreducible Z ↔ (vanishingIdeal Z).IsPrime`
   (`isZariskiIrreducible_iff_isPrime_vanishingIdeal`).
2. **The vanishing ideal is radical** over any field (`vanishingIdeal_isRadical`) — a no-nilpotents
   argument, **not** the strong Nullstellensatz, hence no algebraic-closedness.
3. **Finite-index dimension transport.** `ringKrullDim (MvPolynomial σ k) = Nat.card σ`
   (`ringKrullDim_mvPolynomial_finite`) and the catenary identity over a `Finite` index
   `height p + ringKrullDim (R ⧸ p) = Nat.card σ` (`height_add_ringKrullDim_quotient_eq_card`),
   transported from the `Fin (card σ)` headline through the `renameEquiv` coordinate relabelling.
4. **The bridge headline.** `varietyDim Z` (the Krull dimension of
   `MvPolynomial σ k ⧸ vanishingIdeal Z`), and for `(vanishingIdeal Z).IsPrime`:
   `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`
   (`height_vanishingIdeal_add_varietyDim_eq_card`), with its subtraction reading
   (`height_vanishingIdeal_eq_card_sub_varietyDim`).

Everything here is proved over `[Field k] [Finite σ]` — **no** `[IsAlgClosed k]`, **no** `[CharZero
k]`, **no** field-cardinality constraint (confirmed by the build; the non-vacuity witness fires over
the finite field `ZMod 2`). Nothing is `sorry`/`axiom`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open MvPolynomial Ideal

namespace DLNFibre.Core.Dimension

universe u

variable {k : Type u} [Field k] {σ : Type*}

/-! ## Zariski-closed / irreducible predicates on the point space `σ → k` -/

/-- A subset `Z ⊆ (σ → k)` is **Zariski-closed** when it equals the zero-locus of its own vanishing
ideal — the self-contained, topology-free closure condition (`Z` is cut out by polynomials). -/
def IsZariskiClosed (Z : Set (σ → k)) : Prop :=
  Z = zeroLocus k (vanishingIdeal k Z)

/-- `Z ⊆ (σ → k)` is **Zariski-irreducible** when its image in `Spec (MvPolynomial σ k)` under
`pointToPoint` is irreducible — the point-space irreducibility read through the prime spectrum. -/
def IsZariskiIrreducible (Z : Set (σ → k)) : Prop :=
  IsIrreducible (MvPolynomial.pointToPoint (k := k) (K := k) '' Z)

/-! ## The vanishing ideal is radical (over any field) -/

/-- The vanishing ideal of any subset of `σ → k` is **radical**, over ANY field `k` (no
algebraic-closedness, no Nullstellensatz): if `pⁿ` vanishes on `Z` then `(p x)ⁿ = 0` at each
`x ∈ Z`, so `p x = 0` (a field has no nonzero nilpotents), i.e. `p` vanishes on `Z`. The proof is
the no-nilpotents argument over a field — **not** the strong Nullstellensatz, so `[IsAlgClosed k]`
is not needed. -/
theorem vanishingIdeal_isRadical (Z : Set (σ → k)) :
    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsRadical := by
  intro p hp
  obtain ⟨n, hn⟩ := hp
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hn ⊢
  intro x hx
  have h2 := hn x hx
  rw [map_pow] at h2
  exact pow_eq_zero_iff (n := n) (by rintro rfl; simp at h2) |>.mp h2

/-- **Irreducible ⟺ prime vanishing ideal.** `Z` is Zariski-irreducible iff its vanishing ideal is
prime — the algebraic translation of geometric irreducibility, via the `pointToPoint` image and
`PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`. -/
theorem isZariskiIrreducible_iff_isPrime_vanishingIdeal (Z : Set (σ → k)) :
    IsZariskiIrreducible Z ↔ (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime := by
  unfold IsZariskiIrreducible
  rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime, vanishingIdeal_pointToPoint]

/-! ## Finite-index dimension transport: the catenary identity over a `Fintype` index -/

/-- The Krull dimension of `MvPolynomial σ k` over a finite index `σ` is `Nat.card σ` (a field has
Krull dimension `0`). -/
theorem ringKrullDim_mvPolynomial_finite [Finite σ] :
    ringKrullDim (MvPolynomial σ k) = (Nat.card σ : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- **The catenary identity over a `Fintype` index (`WithBot ℕ∞` form).** For a prime `p` of
`MvPolynomial σ k` (`σ` finite, `k` any field), `height p + ringKrullDim (R ⧸ p) = Nat.card σ`.
Transported from the `Fin (card σ)` headline `height_add_ringKrullDim_quotient_eq` (the
polynomial-ring catenary equality) through the `renameEquiv` coordinate relabelling. -/
theorem height_add_ringKrullDim_quotient_eq_card [Finite σ] (p : Ideal (MvPolynomial σ k))
    [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ p) = (Nat.card σ : WithBot ℕ∞) := by
  haveI : Fintype σ := Fintype.ofFinite _
  set e : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin (Fintype.card σ)) k :=
    MvPolynomial.renameEquiv k (Fintype.equivFin σ) with he
  set q : Ideal (MvPolynomial (Fin (Fintype.card σ)) k) :=
    p.map (e : MvPolynomial σ k →+* MvPolynomial (Fin (Fintype.card σ)) k) with hq
  haveI : q.IsPrime := by rw [hq]; exact Ideal.map_isPrime_of_equiv e
  have hheight : q.height = p.height := height_map_algEquiv e p
  have hdim : ringKrullDim (MvPolynomial (Fin (Fintype.card σ)) k ⧸ q)
      = ringKrullDim (MvPolynomial σ k ⧸ p) :=
    ringKrullDim_quotient_map_algEquiv e p
  have key := height_add_ringKrullDim_quotient_eq k (Fintype.card σ) q
  rw [hheight, hdim] at key
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast key

/-! ## The variety dimension and the bridge headline -/

/-- The **variety dimension** of `Z ⊆ (σ → k)`: the Krull dimension of the coordinate ring
`MvPolynomial σ k ⧸ vanishingIdeal Z` of `Z`'s Zariski closure, as an `ℕ∞` (the `⊥` from a trivial
quotient — absent here, since the relevant `vanishingIdeal Z` is prime — defaulting to `0`). It is
the dimension of `Z` itself exactly when `Z` is Zariski-closed (`IsZariskiClosed`). -/
noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0

/-- **The codimension bridge (additive, `ℕ∞`).** For an irreducible variety `Z ⊆ (σ → k)` — i.e.
`(vanishingIdeal Z).IsPrime` — the height of its vanishing ideal plus its variety dimension equals
the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
catenary identity over `σ`, read at the prime `vanishingIdeal Z`. Geometric codimension `=` ambient
`−` variety dimension, in lossless additive form. -/
theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
  haveI : Nontrivial (MvPolynomial σ k ⧸ vanishingIdeal k Z) :=
    Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  have hne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≠ ⊥ :=
    fun h ↦ by simpa [h] using
      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k Z)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [varietyDim, ← hm, WithBot.unbotD_coe]
  rw [← hm] at key
  exact_mod_cast key

/-- **The codimension bridge (subtraction, `ℕ∞`).** Equivalent reading of the additive bridge:
`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
ambient dimension minus the variety dimension. -/
theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
  have hne : varietyDim Z ≠ ⊤ := by
    intro h
    rw [h, add_top] at hadd
    exact (ENat.coe_ne_top (Nat.card σ)) hadd.symm
  exact (ENat.addLECancellable_of_ne_top hne).eq_tsub_of_add_eq hadd

/-! ## Non-vacuity witness (field-general — any field, any finite index) -/

/-- Non-vacuity witness for the catenary identity, over an **arbitrary** field `k` and finite index
`σ` (no `[IsAlgClosed]`, no infinitude): at the bottom prime `⊥` of `MvPolynomial σ k` (prime since
the polynomial ring over a field is a domain), the identity fires —
`height ⊥ + ringKrullDim (R ⧸ ⊥) = Nat.card σ`. The hypothesis `[Finite σ]` and the prime instance
are the only inputs; the field is unconstrained, so the bridge is genuinely field-general. -/
example [Finite σ] :
    ((⊥ : Ideal (MvPolynomial σ k)).height : WithBot ℕ∞)
      + ringKrullDim (MvPolynomial σ k ⧸ (⊥ : Ideal (MvPolynomial σ k)))
      = (Nat.card σ : WithBot ℕ∞) :=
  height_add_ringKrullDim_quotient_eq_card ⊥

end DLNFibre.Core.Dimension
