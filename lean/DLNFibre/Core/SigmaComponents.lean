import DLNFibre.Core.SigmaStratification
import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.CThetaGeometric
import DLNFibre.Core.MinimalPrime.Finite
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# `DLNFibre.Core.SigmaComponents` — components of `Σ̄^r` and the count `θ` (Phase G3 / θ)

The topology of the closed rank-`≤ r` product locus `Σ̄^r = productRankLocusLE d r`, building on the
set-level orbit stratification `Σ̄^r = ⋃_M Ō_M` (G2, `Core.SigmaStratification`) and the per-orbit
geometry (`Ō_M = orbitRankLocus M` irreducible + prime vanishing ideal, `Core.OrbitClosure`;
geometric codimension, `Core.CThetaGeometric`). Working on the prime spectrum
`PrimeSpectrum (MvPolynomial (RepCoord d) k)` (where the union / minimal-primes algebra lives),
via the **aggregate vanishing ideal** of `Σ̄^r`:

* **G3 — components = maximal `Ō_M`.** The irreducible components of (the Spec-incarnation of)
  `Σ̄^r` are exactly the inclusion-minimal orbit ideals `vanishingIdeal Ō_M` over the corner-`≤ r`
  family — equivalently the **maximal** orbit closures `Ō_M` in orbit-closure order. The bridge:
  the aggregate ideal `sigmaIdeal d r := vanishingIdeal (canonicalCoord d '' Σ̄^r)` is the `sInf` of
  the finite family of prime orbit ideals (G2 + `vanishingIdeal` turns unions into infs), so its
  minimal primes (= irreducible components of `zeroLocus`, Mathlib
  `Ideal.minimalPrimes.equivIrreducibleComponents`) are the inclusion-minimal members of the family.
  (Paper Cor 4.4(b) prints "minimal elements of `R^{≤r}`"; the geometrically-correct object is the
  inclusion-**maximal** orbit closures = inclusion-**minimal** vanishing ideals — settled by the
  worked `(2,2,2)`/`(2,3,2)` examples. The caveat is co-located at `minimalPrimes_sigmaIdeal_eq`.)

* **θ — top-dimensional components are the minimal-codimension orbit closures.** A corner-`≤ r`
  `Ō_M` of minimal geometric codimension (`codimRepCanonical`, the LANDED Voigt codim) is a component
  (`orbitRankLocus_minCodim_mem_minimalPrimes`), via the strict drop of `Ideal.height` under proper
  prime inclusion. The COUNT `numTop d r = #top-dim components` is a roadmap step (the
  Kostant-partition ↔ orbit-ideal count-bijection), NOT proved here.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The aggregate vanishing ideal of `Σ̄^r` and its orbit-ideal family -/

/-- The family of (prime) orbit vanishing ideals over the corner-`≤ r` tuples: the image of
`M ↦ vanishingIdeal (canonicalCoord d '' Ō_M)` over `{M | (mult d M).rank ≤ r}`. -/
noncomputable def orbitIdeals (d : Fin (N + 1) → ℕ) (r : ℕ) :
    Set (Ideal (MvPolynomial (RepCoord d) k)) :=
  (fun M : Tuple (k := k) d ↦
      MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
        (canonicalCoord d '' orbitRankLocus M)) ''
    {M | (mult d M).rank ≤ r}

/-- The padded bounded rank pattern of `M`: the entry `(i, j)` is `rankPattern M i j` (capped into
`Fin ((univ.sup d) + 1)` via the rank bound `r_{ij} ≤ d_i`) for `i ≤ j`, and `0` off the triangle.
A finite-type invariant of `M` that determines its orbit ideal. -/
noncomputable def rpBounded (d : Fin (N + 1) → ℕ) (M : Tuple (k := k) d) :
    Fin (N + 1) × Fin (N + 1) → Fin (Finset.univ.sup d + 1) :=
  fun p ↦ if h : p.1 ≤ p.2 then
    ⟨rankPattern d M p.1 p.2 h, by
      have hle : rankPattern d M p.1 p.2 h ≤ d p.1 := by
        rw [rankPattern]
        exact (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin _)
      have : d p.1 ≤ Finset.univ.sup d := Finset.le_sup (Finset.mem_univ _)
      omega⟩
  else 0

/-- The family map `M ↦ vanishingIdeal (Ō_M)` factors through `rpBounded`: equal bounded rank
patterns give equal rank patterns on the triangle, hence equal orbit loci
(`orbitRankLocus_eq_of_rankPattern_eq`), hence equal images and ideals. -/
theorem familyMap_factorsThrough_rpBounded (d : Fin (N + 1) → ℕ) :
    (fun M : Tuple (k := k) d ↦
        MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus M)).FactorsThrough (rpBounded (k := k) d) := by
  intro M M' hMM'
  have hrp : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d M i j hij = rankPattern d M' i j hij := by
    intro i j hij
    have h := congrFun hMM' (i, j)
    simp only [rpBounded, dif_pos hij] at h
    exact congrArg Fin.val h
  dsimp only
  rw [orbitRankLocus_eq_of_rankPattern_eq hrp]

/-- The orbit-ideal family is finite: `vanishingIdeal (Ō_M)` depends only on `rankPattern M`, which
takes finitely many values (each entry `≤ d_i`), so the family map factors through the
finite-codomain invariant `rpBounded`. -/
theorem orbitIdeals_finite (d : Fin (N + 1) → ℕ) (r : ℕ) :
    (orbitIdeals (k := k) d r).Finite := by
  obtain ⟨e, he⟩ :=
    (Function.factorsThrough_iff _).mp (familyMap_factorsThrough_rpBounded (k := k) d)
  refine Set.Finite.subset (Set.finite_range e) ?_
  rintro J ⟨M, _, rfl⟩
  exact ⟨rpBounded (k := k) d M, (congrFun he M).symm⟩

/-- **The aggregate vanishing ideal of `Σ̄^r`** (the Spec-side incarnation of the closed locus): the
vanishing ideal of the flattened `Σ̄^r = canonicalCoord d '' productRankLocusLE d r`. -/
noncomputable def sigmaIdeal (d : Fin (N + 1) → ℕ) (r : ℕ) :
    Ideal (MvPolynomial (RepCoord d) k) :=
  MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
    (canonicalCoord d '' productRankLocusLE d r)

/-- **The bridge (G2 ⟹ ideal intersection).** The aggregate ideal of `Σ̄^r` is the `sInf` of the
orbit-ideal family: `vanishingIdeal` turns the G2 union `Σ̄^r = ⋃_M Ō_M` into an intersection. -/
theorem sigmaIdeal_eq_sInf_orbitIdeals (d : Fin (N + 1) → ℕ) (r : ℕ) :
    sigmaIdeal (k := k) d r = sInf (orbitIdeals (k := k) d r) := by
  ext p
  rw [sigmaIdeal, Submodule.mem_sInf]
  constructor
  · -- vanish on Σ̄^r ⟹ vanish on each orbit closure of the family
    intro hp J hJ
    obtain ⟨M, hM, rfl⟩ := hJ
    rw [mem_vanishingIdeal_iff] at hp ⊢
    intro y hy
    obtain ⟨A, hA, rfl⟩ := hy
    -- `canonicalCoord A ∈ canonicalCoord '' Ō_M ⊆ canonicalCoord '' Σ̄^r`
    exact hp _ ⟨A, orbitRankLocus_subset_productRankLocusLE d hM hA, rfl⟩
  · -- vanish on each family member ⟹ vanish on Σ̄^r (by G2: every point is in its own Ō_A)
    intro hp
    rw [mem_vanishingIdeal_iff]
    intro x hx
    obtain ⟨A, hA, rfl⟩ := hx
    rw [mem_productRankLocusLE] at hA
    -- the orbit ideal of `A` (corner `= rank (mult A) ≤ r`) is in the family
    have hmem := hp _ ⟨A, hA, rfl⟩
    rw [mem_vanishingIdeal_iff] at hmem
    exact hmem _ ⟨A, self_mem_orbitRankLocus A, rfl⟩

/-! ## The orbit-closure order = the reversed orbit-ideal order -/

/-- **Inclusion-reversal on orbit closures.** For the flattened orbit closures (Zariski-closed sets),
`vanishingIdeal (Ō_M) ≤ vanishingIdeal (Ō_M') ↔ Ō_M' ⊆ Ō_M`. The `←` is `vanishingIdeal_anti_mono`;
the `→` uses that `Ō_M = zeroLocus (vanishingIdeal Ō_M)` (`isZariskiClosed_orbitRankLocus`). So
"inclusion-minimal orbit ideal" `=` "maximal orbit closure" in the orbit-closure (rank-pattern)
order — the bridge that turns `minimalPrimes_sigmaIdeal_eq` into a statement about maximal `Ō_M`. -/
theorem vanishingIdeal_orbitRankLocus_le_iff (d : Fin (N + 1) → ℕ)
    (M M' : Tuple (k := k) d) :
    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (canonicalCoord d '' orbitRankLocus M)
        ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus M')
      ↔ canonicalCoord d '' orbitRankLocus M' ⊆ canonicalCoord d '' orbitRankLocus M := by
  constructor
  · intro hle
    have hclosed : canonicalCoord d '' orbitRankLocus M
        = MvPolynomial.zeroLocus k
          (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
            (canonicalCoord d '' orbitRankLocus M)) := isZariskiClosed_orbitRankLocus M
    rw [hclosed]
    exact (MvPolynomial.zeroLocus_vanishingIdeal_le _).trans (MvPolynomial.zeroLocus_anti_mono hle)
  · exact MvPolynomial.vanishingIdeal_anti_mono

/-! ## G3 — the minimal primes of `Σ̄^r` are the maximal orbit closures -/

/-- Every member of the orbit-ideal family is prime: it is `vanishingIdeal (Ō_M)`, prime over an
infinite field (`Core.OrbitClosure.isPrime_vanishingIdeal_orbitRankLocus`, `[Infinite k]`). -/
theorem orbitIdeals_isPrime [Infinite k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    {p : Ideal (MvPolynomial (RepCoord d) k)} (hp : p ∈ orbitIdeals (k := k) d r) : p.IsPrime := by
  obtain ⟨M, _, rfl⟩ := hp
  exact isPrime_vanishingIdeal_orbitRankLocus M

/-- **G3 (minimal-primes form).** The minimal primes of the aggregate ideal `sigmaIdeal d r` of
`Σ̄^r` are exactly the **inclusion-minimal** orbit ideals `vanishingIdeal (Ō_M)` over the
corner-`≤ r` family. Since `vanishingIdeal` is order-reversing
(`vanishingIdeal_orbitRankLocus_le_iff`), "inclusion-minimal orbit ideal" = "maximal orbit closure
`Ō_M`" (orbit-closure / rank-pattern order, Thm 3.8 `O_s ⊆ Ō_r ⟺ s ≤ r`): the irreducible components
of `Σ̄^r` are the maximal `Ō_M`.
From the bridge `sigmaIdeal = sInf orbitIdeals` + the general finite-family fact
`Ideal.minimalPrimes_sInf_of_finite_of_isPrime` (`Core.MinimalPrime.Finite`): the `minimalPrimes`
of the `sInf` of a finite family of primes are its inclusion-minimal members. `[Infinite k]`
(for primality).
**Caveat (paper transcription).** Le Halleur–Rimányi Cor 4.4(b) as printed reads "the **minimal**
elements of `R^{≤r}`"; the geometrically-correct object is the inclusion-**maximal** orbit closures =
inclusion-**minimal** vanishing ideals (the all-zero pattern is the order-minimal one and sits inside
every closure, so is never a component). Settled by the worked `(2,2,2)`/`(2,3,2)` examples (recon
thread 02); this is what the theorem proves. -/
theorem minimalPrimes_sigmaIdeal_eq [Infinite k] (d : Fin (N + 1) → ℕ) (r : ℕ) :
    (sigmaIdeal (k := k) d r).minimalPrimes
      = {p | p ∈ orbitIdeals (k := k) d r ∧ ∀ q ∈ orbitIdeals (k := k) d r, q ≤ p → p ≤ q} := by
  rw [sigmaIdeal_eq_sInf_orbitIdeals]
  exact Ideal.minimalPrimes_sInf_of_finite_of_isPrime (orbitIdeals d r) (orbitIdeals_finite d r)
    (fun _ hp ↦ orbitIdeals_isPrime d r hp)

/-- **G3 (irreducible-components form).** The irreducible components of (the prime-spectrum
incarnation of) `Σ̄^r`, namely `zeroLocus (sigmaIdeal d r)`, are in inclusion-reversing bijection
with the inclusion-minimal orbit ideals = the maximal orbit closures `Ō_M`. The Mathlib bridge
`Ideal.minimalPrimes.equivIrreducibleComponents`, combined with `minimalPrimes_sigmaIdeal_eq`. -/
noncomputable def irreducibleComponents_sigmaIdeal_equiv [Infinite k] (d : Fin (N + 1) → ℕ)
    (r : ℕ) :
    {p // p ∈ orbitIdeals (k := k) d r ∧ ∀ q ∈ orbitIdeals (k := k) d r, q ≤ p → p ≤ q}
      ≃o (irreducibleComponents (PrimeSpectrum.zeroLocus
        ((sigmaIdeal (k := k) d r : Ideal (MvPolynomial (RepCoord d) k)) :
          Set (MvPolynomial (RepCoord d) k))))ᵒᵈ :=
  (OrderIso.setCongr _ _ (minimalPrimes_sigmaIdeal_eq d r).symm).trans
    (Ideal.minimalPrimes.equivIrreducibleComponents (sigmaIdeal (k := k) d r))

/-! ## θ — the top-dimensional components are the minimal-codimension orbit closures

The geometric "top-dimensional = irreducible component" content: a corner-`≤ r` orbit closure of
**minimal geometric codimension** (`codimRepCanonical`, the LANDED Voigt codim) is an irreducible
component of `Σ̄^r`. The mechanism is the strict drop of `Ideal.height` under proper prime inclusion
(`Ideal.height_strict_mono_of_is_prime`): a non-maximal `Ō_M` sits strictly inside another corner
closure, whose ideal is strictly smaller, so its height is strictly *larger* — i.e. the non-maximal
`Ō_M` has strictly larger codimension and cannot attain the minimum. Hence a min-codimension orbit
closure is automatically maximal, i.e. a component. The COUNT `numTop d r` = #top-dimensional
components is the further step requiring the Kostant-partition ↔ orbit-ideal bijection (see the
module roadmap / statement card — NOT claimed here). -/

/-- The coordinate ring `MvPolynomial (RepCoord d) k` has finite Krull dimension (`= Nat.card`), so
every ideal has finite height — the hypothesis the strict-height brick needs. -/
instance finiteRingKrullDim_mvPolynomial_repCoord (d : Fin (N + 1) → ℕ) :
    FiniteRingKrullDim (MvPolynomial (RepCoord d) k) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top, ringKrullDim_mvPolynomial_finite]
  refine ⟨WithBot.natCast_ne_bot _, ?_⟩
  have : ((Nat.card (RepCoord d) : ℕ∞) : WithBot ℕ∞) ≠ ⊤ := by
    rw [Ne, WithBot.coe_eq_top]; exact ENat.coe_ne_top _
  convert this using 2

/-- **The geometric codimension of `Ō_M` is the height of its orbit ideal** (definitional): the
LANDED `codimRepCanonical (orbitRankLocus M)` is exactly `(vanishingIdeal (Ō_M)).height`, the
prime-height feeding the component / `θ` count. -/
theorem codimRepCanonical_orbitRankLocus_eq_height (d : Fin (N + 1) → ℕ)
    (M : Tuple (k := k) d) :
    codimRepCanonical (orbitRankLocus M)
      = (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus M)).height := rfl

/-- **θ (top-dimensional ⟹ component).** A corner-`≤ r` orbit closure `Ō_M` of **minimal** geometric
codimension among the corner-`≤ r` family is a minimal prime of `sigmaIdeal d r`, i.e. an irreducible
component of `Σ̄^r` — the geometric "min-codim is top-dimensional, hence a component" content. If
`Ō_M` were not maximal, some corner closure `Ō_M'` would strictly contain it (`Ō_M ⊊ Ō_M'`), so
`vanishingIdeal Ō_M' ⊊ vanishingIdeal Ō_M` and the strict-height brick
(`Ideal.height_strict_mono_of_is_prime`) forces `codim Ō_M' < codim Ō_M`, contradicting minimality.
`[Infinite k]` (for primality of the orbit ideals). -/
theorem orbitRankLocus_minCodim_mem_minimalPrimes [Infinite k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (M : Tuple (k := k) d) (hM : (mult d M).rank ≤ r)
    (hmin : ∀ M' : Tuple (k := k) d, (mult d M').rank ≤ r →
      codimRepCanonical (orbitRankLocus M) ≤ codimRepCanonical (orbitRankLocus M')) :
    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (canonicalCoord d '' orbitRankLocus M)
      ∈ (sigmaIdeal (k := k) d r).minimalPrimes := by
  rw [minimalPrimes_sigmaIdeal_eq]
  refine ⟨⟨M, hM, rfl⟩, ?_⟩
  rintro q ⟨M', hM', rfl⟩ hle
  -- `q = vanishingIdeal Ō_M' ≤ vanishingIdeal Ō_M`. If strict, height strictly drops — contra min.
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq.ge
  · -- strict: the orbit ideal of M' is prime, finite height; strict-mono gives codim Ō_M' < codim Ō_M
    haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
        (canonicalCoord d '' orbitRankLocus M')).IsPrime := isPrime_vanishingIdeal_orbitRankLocus M'
    have hstrict := Ideal.height_strict_mono_of_is_prime (R := MvPolynomial (RepCoord d) k) hlt
    rw [← codimRepCanonical_orbitRankLocus_eq_height, ← codimRepCanonical_orbitRankLocus_eq_height]
      at hstrict
    exact absurd (hmin M' hM') (not_le.mpr hstrict)

section Witness

/-! ## Non-vacuity witness — `(2,2,2)`, `r = 0`, over `AlgebraicClosure ℚ`

The zero-product locus `Σ̄^0` of `(2,2,2)` over an algebraically closed field. The zero tuple has
product `0` (rank `0 ≤ 0`), so it lies in `Σ̄^0` and its orbit ideal is in the family `orbitIdeals
d222 0`; the bridge `sigmaIdeal = sInf orbitIdeals` and the G3 minimal-primes characterisation fire.
This is the geometric side of the LANDED combinatorial cross-check (`Core.CTheta`:
`numTop_d222_zero = 1`, three Kostant partitions are maximal so three components, one top-dimensional)
— here the machinery (family nonempty, `sigmaIdeal` the `sInf`, G3 — which needs only `[Infinite k]`)
is shown to fire on the concrete `AlgebraicClosure ℚ` witness. -/

/-- The zero tuple of `(2,2,2)` over `AlgebraicClosure ℚ` lies in the zero-product locus `Σ̄^0`:
its product is `0`, rank `0 ≤ 0`. -/
theorem zero_mem_productRankLocusLE_d222 :
    (0 : Tuple (k := AlgebraicClosure ℚ) dWitness) ∈ productRankLocusLE dWitness 0 := by
  rw [mem_productRankLocusLE]
  have hz : mult dWitness (0 : Tuple (k := AlgebraicClosure ℚ) dWitness) = 0 := by
    -- `mult = A₂ · (A₁ · 1)`; with `A₂ = 0` the last left-factor kills the product.
    change multPrefix dWitness 0 (Fin.last 2) = 0
    rw [show (Fin.last 2 : Fin 3) = (1 : Fin 2).succ from rfl, multPrefix_succ,
      Pi.zero_apply, Matrix.zero_mul]
  rw [hz, Matrix.rank_zero]

/-- The orbit ideal of the zero tuple is in the corner-`0` family — `orbitIdeals d222 0` is
nonempty, so the G3 component machinery has content on `(2,2,2)`. -/
theorem orbitIdeals_d222_zero_nonempty :
    (orbitIdeals (k := AlgebraicClosure ℚ) dWitness 0).Nonempty :=
  ⟨_, ⟨0, zero_mem_productRankLocusLE_d222, rfl⟩⟩

/-- The G3 bridge fires on `(2,2,2)`, `r = 0`: the aggregate ideal of `Σ̄^0` is the `sInf` of its
(nonempty, finite) orbit-ideal family. -/
example :
    sigmaIdeal (k := AlgebraicClosure ℚ) dWitness 0
      = sInf (orbitIdeals (k := AlgebraicClosure ℚ) dWitness 0) :=
  sigmaIdeal_eq_sInf_orbitIdeals dWitness 0

/-- G3 (minimal-primes form) instantiated on `(2,2,2)`, `r = 0`: the components of `Σ̄^0` are the
inclusion-minimal orbit ideals of the corner-`0` family. -/
example :
    (sigmaIdeal (k := AlgebraicClosure ℚ) dWitness 0).minimalPrimes
      = {p | p ∈ orbitIdeals (k := AlgebraicClosure ℚ) dWitness 0
          ∧ ∀ q ∈ orbitIdeals (k := AlgebraicClosure ℚ) dWitness 0, q ≤ p → p ≤ q} :=
  minimalPrimes_sigmaIdeal_eq dWitness 0

end Witness

end DLNFibre.Core
