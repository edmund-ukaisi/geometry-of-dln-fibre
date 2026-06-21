import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.NoetherNormalization
import DLNFibre.Core.IntegralDimension
import DLNFibre.Core.PolynomialDimension
import DLNFibre.Core.NoetherMonicPositioning

/-!
# Affine-domain dimension formula / equidimensionality (network-free engine)

The **L4d** layer: lift the polynomial-ring catenary equality
`height_add_ringKrullDim_quotient_eq` (L5, `Core.NoetherMonicPositioning`) to a finite-type domain
`A = R ⧸ I` over a field (`R = MvPolynomial (Fin n) k`, `I` prime). For a prime `p` of `A`:

* `affine_domain_height_add_ringKrullDim_quotient_eq` :
    `Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A`  (equidimensionality).

* `height_eq_ringKrullDim_of_isMaximal` : for `m` maximal, `Ideal.height m = ringKrullDim A`
  (equidimensionality at closed points).

* `ringKrullDim_localizationAtPrime_isMaximal_eq` : for `m` maximal,
  `ringKrullDim (Localization.AtPrime m) = ringKrullDim A` (local ↔ global dimension at a closed
  point) — the feed-in to the smooth ⟹ regular bridge.

## Route — Noether normalization + integral height transport (reusing L5, no catenary re-induction)

The single new ingredient is the **integral height-transport** lemma
`height_under_eq_of_isIntegral`: for an integral injective extension `R → S` with `R` an
integrally-closed Noetherian domain and `S` a domain, a prime `P` of `S` and its contraction
`p = P.under R` have equal height. The `≤` direction is going-up (`comap` is strictly monotone on
the spectrum, `strictMono_comap_of_isIntegral`); the `≥` direction is going-down, supplied by
Mathlib's classical theorem `Algebra.HasGoingDown` for integral extensions of an integrally closed
domain (`@[stacks 00H8]`) via `Ideal.exists_ltSeries_of_hasGoingDown`. No new catenary induction is
needed — the polynomial-ring catenary content is L5, reused as a black box.

Given `A = R ⧸ I`, Noether-normalize (`exists_integral_inj_algHom_of_quotient`) to an integral
injective `g : B = MvPolynomial (Fin s) k →ₐ[k] A`. The base `B` is a polynomial ring over a field,
hence an integrally-closed (UFD) Noetherian domain. With `q = p.comap g`, height-transport gives
`height_A p = height_B q`; the induced quotient map `B ⧸ q ↪ A ⧸ p` is integral injective so
`dim (A ⧸ p) = dim (B ⧸ q)` (L5.4); and `dim A = dim B = s` (L5.4 + L5.0). Then L5 on `B` at the
prime `q` (`height_B q + dim (B ⧸ q) = s`) assembles the equality additively, no `ℕ∞` subtraction.
-/

open PrimeSpectrum

namespace DLNFibre.Core

/-! ### Integral height transport (the one new general brick) -/

/-- **Integral height transport.** For an integral injective extension `R → S` with `R` an
integrally-closed Noetherian domain and `S` a domain, a prime `P` of `S` and its contraction
`P.under R` have equal height. The `≤` direction is going-up (`comap` strictly monotone); the `≥`
direction is going-down (`Algebra.HasGoingDown`, present for integral extensions of an integrally
closed domain). -/
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

/-- **Affine-domain dimension formula (equidimensionality).** For `R = MvPolynomial (Fin n) k`
(`k` a field), a prime `I`, the domain `A = R ⧸ I`, and a prime `p` of `A`:
`Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Proved by Noether-normalizing `A`,
transporting the height of `p` to its contraction in the polynomial base, and reusing the L5
polynomial-ring catenary equality on the base. -/
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
  -- L5 on the polynomial base `B` at the prime `q`.
  have hL5 : (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = (s : WithBot ℕ∞) :=
    height_add_ringKrullDim_quotient_eq k s q
  -- Assemble additively.
  rw [hdimA, ← hL5, htrans, hdimQuot]

/-! ### The maximal-ideal corollary (equidimensionality at closed points) -/

/-- **Equidimensionality at a closed point.** For `A = R ⧸ I` a finite-type domain over a field and
`m` a maximal ideal of `A`, `Ideal.height m = ringKrullDim A` (`A ⧸ m` a field, dimension `0`). -/
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

/-- **Local ↔ global dimension at a closed point.** For `A = R ⧸ I` a finite-type domain over a
field and `m` a maximal ideal, the local ring `Localization.AtPrime m` has Krull dimension equal to
`ringKrullDim A`. Feeds the smooth ⟹ regular bridge (L4a). -/
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

end DLNFibre.Core
