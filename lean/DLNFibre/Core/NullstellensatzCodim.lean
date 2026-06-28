import DLNFibre.Core.NoetherMonicPositioning
import DLNFibre.Core.OrbitCodim
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# `DLNFibre.Core.NullstellensatzCodim` — the point-space ↔ `PrimeSpectrum` codimension bridge (L0)

Over an algebraically closed field `k` and a finite coordinate index `σ` (our `RepCoord d`), this
module connects the **geometric** codimension of a Zariski-closed subset `Z ⊆ (σ → k)` — the
`Ideal.height` of its vanishing ideal, the quantity `codimRep` reads — to the **variety dimension**
of `Z` (the Krull dimension of its coordinate ring) via the catenary identity for affine space.

The catenary dimension formula `Ideal.height p + ringKrullDim (R ⧸ p) = n` for `R = MvPolynomial
(Fin n) k` (any field) is **proved** in `Core.NoetherMonicPositioning`
(`height_add_ringKrullDim_quotient_eq`, "L5"). Here we:

1. **Nullstellensatz pieces** (Mathlib's `MvPolynomial.vanishingIdeal`/`zeroLocus`, strong
   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
   (`vanishingIdeal_isRadical`); `Z` irreducible ⟺ `vanishingIdeal Z` is **prime**
   (`isZariskiIrreducible_iff_isPrime_vanishingIdeal`, through the `pointToPoint` image and
   `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`); a closed `Z` with prime vanishing
   ideal is **nonempty** (`nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal`, weak
   Nullstellensatz from the strong one).
2. **Finite-index dimension transport.** L5 is over `Fin n`; we transport it to `MvPolynomial σ k`
   for a `Fintype σ` via `Fintype.equivFin`/`MvPolynomial.renameEquiv` and the `k`-algebra-equiv
   transport lemmas (`height_map_algEquiv`, `ringKrullDim_quotient_map_algEquiv`):
   `height_add_ringKrullDim_quotient_eq_card`, `ringKrullDim (MvPolynomial σ k) = Nat.card σ`.
3. **The bridge headline.** For `(vanishingIdeal Z).IsPrime` (the algebraic content of "`Z`
   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
   truncated subtraction is lossy, so the additive identity is the bedrock form), with the
   `WithBot ℕ∞` companion and a subtraction corollary. Specialised to `codimRep`/`codimRepCanonical`
   for the geometry layer.

`[IsAlgClosed k]` is a **hypothesis**, not a citation. Everything is proved; nothing is `sorry`/
`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
coordinate ring of `Z`'s Zariski closure — it is the variety dimension of `Z` itself precisely when
`Z` is Zariski-closed (`IsZariskiClosed`), the geometric reading carried by that predicate.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open MvPolynomial Ideal

namespace DLNFibre.Core

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

/-! ## Nullstellensatz pieces (over an algebraically closed field) -/

/-- The vanishing ideal of any subset of `σ → k` is **radical** (over `[IsAlgClosed k]`): by the
strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
theorem vanishingIdeal_isRadical [IsAlgClosed k] [Finite σ] (Z : Set (σ → k)) :
    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsRadical := by
  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
    conv_lhs =>
      rw [← (zeroLocus_vanishingIdeal_galoisConnection (σ := σ) (k := k) (K := k)).u_l_u_eq_u Z,
        vanishingIdeal_zeroLocus_eq_radical (K := k)]
  rw [h]; exact radical_isRadical _

/-- **Irreducible ⟺ prime vanishing ideal.** `Z` is Zariski-irreducible iff its vanishing ideal is
prime — the algebraic translation of geometric irreducibility, via the `pointToPoint` image and
`PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`. -/
theorem isZariskiIrreducible_iff_isPrime_vanishingIdeal (Z : Set (σ → k)) :
    IsZariskiIrreducible Z ↔ (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime := by
  unfold IsZariskiIrreducible
  rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime, vanishingIdeal_pointToPoint]

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

/-! ## Finite-index dimension transport: the catenary identity over a `Fintype` index -/

/-- The Krull dimension of `MvPolynomial σ k` over a finite index `σ` is `Nat.card σ` (a field has
Krull dimension `0`). -/
theorem ringKrullDim_mvPolynomial_finite [Finite σ] :
    ringKrullDim (MvPolynomial σ k) = (Nat.card σ : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- **The catenary identity over a `Fintype` index (`WithBot ℕ∞` form).** For a prime `p` of
`MvPolynomial σ k` (`σ` finite, `k` any field), `height p + ringKrullDim (R ⧸ p) = Nat.card σ`.
Transported from the `Fin (card σ)` headline `height_add_ringKrullDim_quotient_eq` (L5) through the
`renameEquiv` coordinate relabelling. -/
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

/-! ## Non-vacuity witness -/

/-- The vanishing ideal of the **whole space** `⊤ ⊆ (σ → k)` is `⊥` over any algebraically closed
(hence infinite) field: a polynomial vanishing at every point of `σ → k` is `0`
(`MvPolynomial.funext` over an infinite integral domain). -/
theorem vanishingIdeal_univ_eq_bot [IsAlgClosed k] :
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

end DLNFibre.Core
