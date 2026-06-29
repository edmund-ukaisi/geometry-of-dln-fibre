import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.NoetherNormalization
import DLNFibre.Core.Dimension.Integral
import DLNFibre.Core.Dimension.Basic
import DLNFibre.Core.Dimension.Catenary

/-!
# Dimension formula / equidimensionality for finite-type domains over a field

This file lifts the polynomial-ring catenary equality
`DLNFibre.Core.Dimension.height_add_ringKrullDim_quotient_eq` (`Core.Dimension.Catenary`) to an
arbitrary **finite-type domain** `A = k[x₁,…,xₙ] ⧸ I` over a field `k` (`I` prime). For a prime `p`
of `A`:

* `affine_domain_height_add_ringKrullDim_quotient_eq` :
    `Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A` (the dimension formula —
    equidimensionality, [Stacks, Tag 00OS]).

* `height_eq_ringKrullDim_of_isMaximal` : for `m` maximal, `Ideal.height m = ringKrullDim A`
  (every maximal ideal has height `dim A` — equidimensionality at closed points,
  [Stacks, Tag 00OS]).

* `ringKrullDim_localizationAtPrime_isMaximal_eq` : for `m` maximal,
  `ringKrullDim (Localization.AtPrime m) = ringKrullDim A` (local ↔ global dimension at a closed
  point, [Stacks, Tag 00OS] — `dim A = dim Aₘ`). This is the feed-in to the smooth ⟹ regular-local
  bridge.

[Stacks, Tag 00OS] (Lemma 10.114.4) is the equidimensionality statement for a finite-type domain
over a field: every maximal chain of primes has length `dim S`, equivalently `dim S = dim Sₘ` for
every maximal `m`. The two closed-point corollaries are the verbatim `dim S = dim Sₘ`. The headline
dimension formula `height p + dim (A ⧸ p) = dim A` at an arbitrary prime is a **restatement** of the
same equidimensionality (via finite-type catenary): the verbatim displayed form is the
maximal-ideal/equidimensionality corollary, and Codex notes 00P2 as the closest literal tag for the
arbitrary-prime form, though none displays it exactly. All three carry the `@[stacks 00OS]` tag —
true and on-point.

This file mirrors the eventual Mathlib home for the dimension theory of finitely generated algebras
(distinct from `Mathlib.RingTheory.KrullDimension.Catenary`, the polynomial-ring identity), and
builds on `Core.Dimension.Catenary` (the polynomial-ring catenary equality, reused as a black box —
no catenary re-induction), `Core.Dimension.Integral` (integral-extension dimension invariance), and
`Core.Dimension.Basic` (`dim k[x₁,…,xₙ] = n`).

## Route — Noether normalization + integral height transport

The single new ingredient is the **integral height-transport** lemma
`height_under_eq_of_isIntegral`: for an integral injective extension `R → S` with `R` an
integrally-closed Noetherian domain and `S` a domain, a prime `P` of `S` and its contraction
`p = P.under R` have equal height. The `≤` direction is going-up (`comap` is strictly monotone on
the spectrum, `strictMono_comap_of_isIntegral`); the `≥`
direction is going-down, supplied by Mathlib's classical `Algebra.HasGoingDown` for integral
extensions of an integrally closed domain ([Stacks, Tag 00H8]) via
`Ideal.exists_ltSeries_of_hasGoingDown`.

Given `A = R ⧸ I`, Noether-normalize (`exists_integral_inj_algHom_of_quotient`) to an integral
injective `g : B = MvPolynomial (Fin s) k →ₐ[k] A`. The base `B` is a polynomial ring over a field,
hence an integrally-closed (UFD) Noetherian domain. With `q = p.comap g`, height-transport gives
`height_A p = height_B q`; the induced quotient map `B ⧸ q ↪ A ⧸ p` is integral injective so
`dim (A ⧸ p) = dim (B ⧸ q)`; and `dim A = dim B = s`. Then the polynomial-ring catenary equality on
`B` at the prime `q` (`height_B q + dim (B ⧸ q) = s`) assembles the formula additively — no `ℕ∞`
subtraction.
-/

open PrimeSpectrum

namespace DLNFibre.Core.Dimension

/-! ### Integral height transport (the one new general brick) -/

/-- **Integral height transport.** For an integral injective extension `R → S` with `R` an
integrally-closed Noetherian domain and `S` a domain, a prime `P` of `S` and its contraction
`P.under R` have equal height. The `≤` direction is going-up (`comap` strictly monotone); the `≥`
direction is going-down ([Stacks, Tag 00H8], `Algebra.HasGoingDown`, present for integral extensions
of an integrally closed domain). -/
theorem height_under_eq_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  set p : Ideal R := P.under R with hp
  haveI : p.IsPrime := inferInstance
  haveI : P.LiesOver p := inferInstance
  apply le_antisymm
  · -- going-up: comap a chain below `P` (strictly monotone) into a chain below `p`.
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_eq_iSup_last_eq]
    refine iSup₂_le fun l hl ↦ ?_
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]
    have hmap : (l.map (comap (algebraMap R S))
        strictMono_comap_of_isIntegral).last = ⟨p, ‹_›⟩ := by
      rw [LTSeries.last_map, hl]; rfl
    calc (l.length : ℕ∞)
        = (l.map (comap (algebraMap R S))
            strictMono_comap_of_isIntegral).length := by rw [LTSeries.map_length]
      _ ≤ Order.height (⟨p, ‹_›⟩ : PrimeSpectrum R) :=
          Order.length_le_height (le_of_eq hmap)
  · -- going-down: lift a chain below `p` realizing `height p` to a chain below `P`.
    haveI : p.FiniteHeight := inferInstance
    obtain ⟨l, hlast, hlen⟩ := p.exists_ltSeries_length_eq_height
    haveI : P.LiesOver l.last.asIdeal := by rw [hlast]; exact ‹P.LiesOver p›
    obtain ⟨L, hLlen, hLlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
    have hPh : (L.length : ℕ∞) ≤ P.height := by
      rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]
      exact Order.length_le_height (hLlast ▸ le_rfl)
    calc p.height = (l.length : ℕ∞) := hlen.symm
      _ = (L.length : ℕ∞) := by rw [hLlen]
      _ ≤ P.height := hPh

/-! ### The induced quotient map of a contracted prime is integral injective -/

/-- For an integral injective ring hom `g : B →+* A` and a prime `p` of `A`, the induced quotient
map `B ⧸ (p.comap g) →+* A ⧸ p` is integral and injective. -/
theorem quotientMap_under_isIntegral_injective {B A : Type*} [CommRing B] [CommRing A]
    (g : B →+* A) (hint : g.IsIntegral) (p : Ideal A) [p.IsPrime] :
    Function.Injective (Ideal.quotientMap p g le_rfl) ∧
      (Ideal.quotientMap p g le_rfl).IsIntegral :=
  ⟨Ideal.quotientMap_injective, by
    rw [isIntegral_quotientMap_iff]
    exact RingHom.IsIntegral.trans g (Ideal.Quotient.mk p) hint
      (RingHom.isIntegral_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective)⟩

/-! ### The affine-domain dimension formula -/

/-- **Affine-domain dimension formula (equidimensionality)** ([Stacks, Tag 00OS]). For
`R = MvPolynomial (Fin n) k` (`k` a field), a prime `I`, the finite-type domain `A = R ⧸ I`, and a
prime `p` of `A`: `Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Proved by
Noether-normalizing `A`, transporting the height of `p` to its contraction in the polynomial base,
and reusing the polynomial-ring catenary equality on the base. This arbitrary-prime form is a
**restatement** of 00OS's equidimensionality (the verbatim displayed form is the
maximal-ideal/equidimensionality corollary below); Codex notes 00P2 as the closest literal tag for
the arbitrary-prime form, though none displays it exactly — the `@[stacks 00OS]` tag is true and
on-point. -/
@[stacks 00OS "restatement of equidimensionality as `height p + dim (A ⧸ p) = dim A`"]
theorem affine_domain_height_add_ringKrullDim_quotient_eq
    (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (p : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
  -- Noether-normalize `A = R ⧸ I`.
  obtain ⟨s, _, g, hg_inj, hg_int⟩ :=
    exists_integral_inj_algHom_of_quotient I (Ideal.IsPrime.ne_top ‹_›)
  set A := (MvPolynomial (Fin n) k) ⧸ I
  set B := MvPolynomial (Fin s) k
  haveI : IsDomain A := Ideal.Quotient.isDomain I
  -- Install the algebra/integral structure carried by the ring hom `g`.
  algebraize [g.toRingHom]
  have halg : algebraMap B A = g.toRingHom := rfl
  haveI : Algebra.IsIntegral B A := ⟨hg_int⟩
  -- `dim A = dim B = s`.
  have hdimA : ringKrullDim A = (s : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_integral_injective (f := g.toRingHom) hg_int hg_inj,
      ringKrullDim_mvPolynomial_fin_field]
  -- Contract `p` to a prime `q` of `B`.
  set q : Ideal B := p.comap g.toRingHom with hq
  haveI : q.IsPrime := Ideal.comap_isPrime g.toRingHom p
  have hqunder : p.under B = q := by rw [Ideal.under_def, halg, hq]
  -- Height transport: `height_A p = height_B q`.
  have htrans : p.height = q.height := by
    have := height_under_eq_of_isIntegral (R := B) (S := A)
      (by rw [halg]; exact hg_inj) p
    rwa [hqunder] at this
  -- `dim (A ⧸ p) = dim (B ⧸ q)` via the integral injective induced quotient map.
  obtain ⟨hbar_inj, hbar_int⟩ := quotientMap_under_isIntegral_injective g.toRingHom hg_int p
  have hdimQuot : ringKrullDim (A ⧸ p) = ringKrullDim (B ⧸ q) := by
    have h := ringKrullDim_eq_of_integral_injective
      (f := Ideal.quotientMap p g.toRingHom le_rfl) hbar_int hbar_inj
    -- `quotientMap p g le_rfl : (B ⧸ p.comap g) →+* (A ⧸ p)`, and `q = p.comap g`.
    rwa [← hq] at h
  -- The polynomial-ring catenary equality on the base `B` at the prime `q`.
  have hcat : (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = (s : WithBot ℕ∞) :=
    height_add_ringKrullDim_quotient_eq k s q
  -- Assemble additively.
  rw [hdimA, ← hcat, htrans, hdimQuot]

/-! ### The maximal-ideal corollaries (equidimensionality at closed points) -/

/-- **Equidimensionality at a closed point** ([Stacks, Tag 00OS]). For `A = R ⧸ I` a finite-type
domain over a field and `m` a maximal ideal of `A`, `Ideal.height m = ringKrullDim A` (`A ⧸ m` is a
field, dimension `0`). -/
@[stacks 00OS "every maximal ideal of a finite-type domain has height `dim A`"]
theorem height_eq_ringKrullDim_of_isMaximal
    (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (m : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
  haveI : m.IsPrime := inferInstance
  have hfield : IsField (((MvPolynomial (Fin n) k) ⧸ I) ⧸ m) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp ‹m.IsMaximal›
  have h := affine_domain_height_add_ringKrullDim_quotient_eq k n I m
  rw [ringKrullDim_eq_zero_of_isField hfield, add_zero] at h
  exact h

/-- **Local ↔ global dimension at a closed point** ([Stacks, Tag 00OS], `dim A = dim Aₘ`). For
`A = R ⧸ I` a finite-type domain over a field and `m` a maximal ideal, the local ring
`Localization.AtPrime m` has Krull dimension equal to `ringKrullDim A`. Feeds the smooth ⟹ regular
bridge. -/
@[stacks 00OS "`dim A = dim Aₘ` for a finite-type domain and a maximal ideal `m`"]
theorem ringKrullDim_localizationAtPrime_isMaximal_eq
    (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (m : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
  haveI : m.IsPrime := inferInstance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  exact height_eq_ringKrullDim_of_isMaximal k n I m

/-! ### Non-vacuity witnesses -/

/-- Witness for the height-transport brick: the identity on `MvPolynomial (Fin 1) ℚ` is integral and
injective, and the transport reads `height P = height (P.under R) = height P` for any prime `P`. -/
example (P : Ideal (MvPolynomial (Fin 1) ℚ)) [P.IsPrime] :
    P.height = (P.under (MvPolynomial (Fin 1) ℚ)).height :=
  height_under_eq_of_isIntegral (fun a b h ↦ by simpa using h) P

/-- Witness for the affine-domain formula at the bottom prime of `A = ℚ[x] ⧸ ⊥` (so `A ≅ ℚ[x]`,
dimension `1`): the formula reads `height ⊥ + dim (A ⧸ ⊥) = 0 + 1 = 1 = dim A`, a concrete nonzero
value, the dimension term carrying it. -/
example :
    ((⊥ : Ideal ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)))).height
        : WithBot ℕ∞)
      + ringKrullDim (((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) ⧸
          (⊥ : Ideal ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)))))
      = ringKrullDim ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) :=
  affine_domain_height_add_ringKrullDim_quotient_eq ℚ 1 ⊥ ⊥

/-- Witness that the local↔global corollary fires: for `A = ℚ[x] ⧸ ⊥` and a maximal `m`,
`dim (Localization.AtPrime m) = dim A`. -/
example (m : Ideal ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))))
    [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m)
      = ringKrullDim ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) :=
  ringKrullDim_localizationAtPrime_isMaximal_eq ℚ 1 ⊥ m

/-- The maximal-ideal hypothesis of the two corollaries is satisfiable: every nonzero commutative
ring has a maximal ideal, so the finite-type domain `A = ℚ[x] ⧸ ⊥` carries one. -/
example : ∃ m : Ideal ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))),
    m.IsMaximal :=
  Ideal.exists_maximal _

end DLNFibre.Core.Dimension
