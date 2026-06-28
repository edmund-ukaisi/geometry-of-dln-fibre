import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.IntegralDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `DLNFibre.Core.RadicalCatenary` — the catenary identity for a reducible (radical) locus

The prime catenary `height p + ringKrullDim (R ⧸ p) = card` (`Core.NullstellensatzCodim`,
`height_add_ringKrullDim_quotient_eq_card`) extended to an **arbitrary proper** ideal `I ≠ ⊤` of a
polynomial ring `R = MvPolynomial σ k` (`σ` finite, `k` any field):

> `height I + ringKrullDim (R ⧸ I) = Nat.card σ`.

Geometrically: a reducible variety `V(I) = ⋃ V(pᵢ)` has codimension `= min` component codimension
and dimension `= max` component dimension, and the polynomial ring is catenary, so the two are dual.
The proof is a direct order/chain argument over `PrimeSpectrum`, two inequalities squeezed by
`le_antisymm` (no component-decomposition lemma, no radicality needed):

* **upper bound** `height I + dim (R ⧸ I) ≤ card`: a longest prime chain of `R ⧸ I` maps into the
  primes `⊇ I` of `R`; its head contains a minimal prime `p`, so `dim (R ⧸ I) ≤ coheight p =
  dim (R ⧸ p)`, while `height I ≤ height p`, and the per-prime catenary closes `≤ card`;
* **lower bound** `card ≤ height I + dim (R ⧸ I)`: a minimal prime `p₀` realises `height I`; the
  quotient surjection `R ⧸ I ↠ R ⧸ p₀` gives `dim (R ⧸ p₀) ≤ dim (R ⧸ I)`, and the per-prime
  catenary for `p₀` reads `card = height I + dim (R ⧸ p₀) ≤ height I + dim (R ⧸ I)`.

The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
Zariski-closed `Z` (over any field its vanishing ideal is radical — `vanishingIdeal_isRadical`;
nonempty makes it proper — `vanishingIdeal_ne_top_of_nonempty`), discharging the reducible-locus
catenary that `Core.RouteCAssembly` carries as the named hypotheses `hCatFibre`/`hCatSigma`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open MvPolynomial Ideal Order

namespace DLNFibre.Core

universe u

variable {k : Type u} [Field k] {σ : Type*}

/-! ## A minimal prime realising the height -/

/-- **A minimal prime realises `I.height`.** For a Noetherian ring and a proper ideal `I ≠ ⊤`, some
minimal prime `p ∈ I.minimalPrimes` has `p.height = I.height`. The infimum `I.height = ⨅_{p}
primeHeight p` over the finite nonempty set of minimal primes is attained. -/
theorem exists_minimalPrime_height_eq_height {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hIne : I ≠ ⊤) :
    ∃ p ∈ I.minimalPrimes, p.height = I.height := by
  obtain ⟨p₀, hp₀⟩ := Ideal.nonempty_minimalPrimes hIne
  obtain ⟨p, hp, hpmin⟩ :=
    Set.exists_min_image _ (fun J ↦ J.height)
      I.finite_minimalPrimes_of_isNoetherianRing ⟨p₀, hp₀⟩
  refine ⟨p, hp, ?_⟩
  haveI := Ideal.minimalPrimes_isPrime hp
  apply le_antisymm
  · -- `height p ≤ height I`: `p` minimises `height` over the minimal primes (the `⨅`).
    rw [Ideal.height]
    refine le_iInf₂ (fun J hJ ↦ ?_)
    haveI := Ideal.minimalPrimes_isPrime hJ
    have : @Ideal.primeHeight _ _ J (Ideal.minimalPrimes_isPrime hJ) = J.height :=
      (Ideal.height_eq_primeHeight J).symm
    rw [this]
    exact hpmin J hJ
  · -- `height I ≤ height p`: `height I` is the `⨅`, `p` is one of the minimal primes.
    rw [Ideal.height]
    refine iInf₂_le_of_le p hp ?_
    exact le_of_eq (by rw [← Ideal.height_eq_primeHeight])

/-! ## A top-dimensional component -/

/-- **A minimal prime carries the full quotient dimension.** For a finite-dimensional Noetherian
ring `R` and a proper ideal `I ≠ ⊤`, some minimal prime `p ∈ I.minimalPrimes` has
`ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ p)` — a top-dimensional component. A longest prime chain
of `R ⧸ I` maps (via the
quotient `comap`, strictly monotone) into the primes `⊇ I` of `R`; its head contains a minimal prime
`p`, and the chain's length is `≤ coheight p = ringKrullDim (R ⧸ p)`. -/
theorem exists_minimalPrime_ringKrullDim_quotient_ge {R : Type*} [CommRing R] [IsNoetherianRing R]
    [FiniteRingKrullDim R] (I : Ideal R) (hIne : I ≠ ⊤) :
    ∃ p ∈ I.minimalPrimes, ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ p) := by
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  haveI : FiniteRingKrullDim (R ⧸ I) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top (R := R ⧸ I)]
    refine ⟨?_, ne_top_of_le_ne_top (ringKrullDim_ne_top (R := R)) (ringKrullDim_quotient_le I)⟩
    exact fun h ↦ by simpa [h] using ringKrullDim_nonneg_of_nontrivial (R := R ⧸ I)
  haveI : FiniteDimensionalOrder (PrimeSpectrum (R ⧸ I)) := by
    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum (R ⧸ I))]
    exact ⟨ringKrullDim_ne_bot, ringKrullDim_ne_top⟩
  -- a longest chain `L` of `Spec (R ⧸ I)`, realising the Krull dimension.
  set L := LTSeries.longestOf (PrimeSpectrum (R ⧸ I)) with hL
  have hLlen : ringKrullDim (R ⧸ I) = (L.length : WithBot ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder]
  -- map the chain into `Spec R` via the (strictly monotone) quotient comap.
  have hsm : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  set Lmap := L.map (PrimeSpectrum.comap (Ideal.Quotient.mk I)) hsm with hLmap
  -- the head of the mapped chain is a prime `⊇ I`; pick a minimal prime `p` below it.
  have hheadge : I ≤ Lmap.head.asIdeal := by
    rw [hLmap, LTSeries.head_map, PrimeSpectrum.comap_asIdeal]
    exact (Ideal.mk_ker (I := I)).symm.trans_le (Ideal.ker_le_comap (Ideal.Quotient.mk I))
  obtain ⟨p, hpmem, hple⟩ := Ideal.exists_minimalPrimes_le hheadge
  haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hpmem
  refine ⟨p, hpmem, ?_⟩
  -- `L.length ≤ coheight ⟨p⟩ = dim (R ⧸ p)`.
  have hlen_le : (Lmap.length : ℕ∞) ≤ Order.coheight (⟨p, ‹_›⟩ : PrimeSpectrum R) :=
    Order.length_le_coheight (x := (⟨p, ‹_›⟩ : PrimeSpectrum R)) (p := Lmap) hple
  rw [hLlen, ringKrullDim_quotient_eq_coheight (⟨p, ‹_›⟩ : PrimeSpectrum R)]
  rw [hLmap, LTSeries.map_length] at hlen_le
  exact_mod_cast hlen_le

/-! ## The radical-locus catenary -/

/-- **The reducible-locus catenary.** For `R = MvPolynomial σ k` (`σ` finite, `k` any field) and a
proper ideal `I ≠ ⊤`, `height I + ringKrullDim (R ⧸ I) = Nat.card σ` — the per-prime catenary
carried across the components: `dim (R ⧸ I) = max` dim `= card − min` height `= card − height I`.
Direct chain/coheight squeeze; no radicality needed. -/
theorem height_add_ringKrullDim_quotient_eq_card_of_ne_top [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hIne : I ≠ ⊤) :
    (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I) = (Nat.card σ : WithBot ℕ∞) := by
  set R := MvPolynomial σ k with hR
  set n : WithBot ℕ∞ := (Nat.card σ : WithBot ℕ∞) with hn
  -- the per-prime catenary, restated as `dim (R ⧸ p) = card − height p` in the additive form.
  have hprime : ∀ p : Ideal R, p.IsPrime →
      (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = n := fun p hp ↦
    height_add_ringKrullDim_quotient_eq_card (k := k) (σ := σ) p
  -- `R = MvPolynomial σ k` has finite Krull dimension `Nat.card σ`.
  have hRdim : ringKrullDim R = ((Nat.card σ : ℕ∞) : WithBot ℕ∞) := ringKrullDim_mvPolynomial_finite
  haveI : FiniteRingKrullDim R := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top (R := R), hRdim]
    refine ⟨WithBot.coe_ne_bot, ?_⟩
    rw [Ne, WithBot.coe_eq_top]
    exact ENat.coe_ne_top (Nat.card σ)
  apply le_antisymm
  · -- upper bound: a top-dimensional component `p` has `dim (R ⧸ I) ≤ dim (R ⧸ p)`.
    obtain ⟨p, hpmem, hpdim⟩ := exists_minimalPrime_ringKrullDim_quotient_ge I hIne
    haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hpmem
    have hIp : I ≤ p := hpmem.1.2
    calc (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I)
        ≤ (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) :=
          add_le_add (WithBot.coe_le_coe.mpr (Ideal.height_mono hIp)) hpdim
      _ = n := hprime p ‹_›
  · -- lower bound: a minimal prime `p₀` realising `height I`, with `R ⧸ I ↠ R ⧸ p₀`.
    obtain ⟨p₀, hp₀mem, hp₀ht⟩ := exists_minimalPrime_height_eq_height I hIne
    haveI : p₀.IsPrime := Ideal.minimalPrimes_isPrime hp₀mem
    have hIp₀ : I ≤ p₀ := hp₀mem.1.2
    -- `dim (R ⧸ p₀) ≤ dim (R ⧸ I)` from the quotient surjection `R ⧸ I ↠ R ⧸ p₀`.
    have hdimle : ringKrullDim (R ⧸ p₀) ≤ ringKrullDim (R ⧸ I) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hIp₀)
    -- the per-prime catenary for `p₀`, with `height p₀ = height I`.
    have := hprime p₀ ‹_›
    rw [hp₀ht] at this
    calc n = (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p₀) := this.symm
      _ ≤ (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) := by
          gcongr

/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/

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
