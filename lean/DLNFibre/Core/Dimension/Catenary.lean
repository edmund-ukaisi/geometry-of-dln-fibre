import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.MvPolynomial.Division
import DLNFibre.Core.Dimension.Integral
import DLNFibre.Core.Dimension.Basic

/-!
# Catenary dimension formula for polynomial rings over a field

This file proves the **catenary equality** for the polynomial ring `R = k[x₁,…,xₙ]` over any field
`k`: for a prime `p`,
$$\operatorname{height} p + \dim (R / p) = n.$$
Equivalently, on the spectrum, `height p + coheight p = n` — affine space is *equidimensional*, so
height and coheight are exactly complementary ([Stacks, Tag 00OS]). Mathlib v4.29 has only the `≤`
half of this (assembled here as `height_add_coheight_le` from
`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty` and the polynomial dimension
`dim k[x₁,…,xₙ] = n`); the `≥` half — the content — is proved here by induction on `n`.

This file mirrors the eventual Mathlib home `Mathlib.RingTheory.KrullDimension.Catenary` and builds
on `DLNFibre.Core.Dimension.Integral` (integral-extension dimension invariance) and
`DLNFibre.Core.Dimension.Basic` (`dim k[x₁,…,xₙ] = n`, `dim (R ⧸ p) = coheight p`).

## The `≥` direction, in three pieces

* **Monic positioning** ([Stacks, Tag 00OX], `§ Provenance of the monic-positioning substitution`).
  For a nonzero
  `f : k[x₀,…,xₙ]`, a `k`-algebra automorphism `ψ` makes `ψ f` *monic up to a unit* in `x₀` over
  `k[x₁,…,xₙ]`: `IsUnit (finSuccEquiv k n (ψ f)).leadingCoeff`. Mathlib proves exactly this inside
  its Noether-normalization file via the substitution `T : xᵢ ↦ xᵢ + x₀^(N^i)` (`i ≠ 0`, `x₀ ↦ x₀`),
  `N = 2 + f.totalDegree`, but the construction (`T`, `T_leadingcoeff_isUnit`) is **`private`**. We
  re-expose that machinery in the `MonicPositioning` namespace below — verbatim degree bookkeeping,
  visibility the only change — and read off the one public consequence
  `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`. The substitution uses `x₀`-powers, not generic
  linear combinations, so it is **characteristic- and field-cardinality-free** (finite fields are
  fine; no `Infinite k` / `IsAlgClosed`). See `§ Provenance of the monic-positioning substitution`.

* **The one-variable tower** ([Stacks, Tag 00ON],
  `§ The catenary ≤ direction and the one-variable polynomial tower`). For `A` Noetherian and a
  prime `P` of `A[X]` over `q = P.under A`,
  `height P = height q + height (image of P in (A ⧸ q)[X])`. The extension `A → A[X]` is free hence
  flat, so it satisfies going-down, and this is
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`. After positioning, the peeled fiber has
  height `≥ 1` (`one_le_height_map_quotient_of_monic`), and the monic peel preserves the quotient
  dimension (`ringKrullDim_quotient_eq_under_of_monic`).

* **The induction** (`nat_le_height_add_coheight`). Peels variable `0` at each step, transferring
  height and quotient dimension across the positioning automorphism.

All statements are at the natural generality (`k : Type*` any field). `IsAlgClosed` is **not**
needed anywhere — these are pure dimension facts.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List
open Order PrimeSpectrum

namespace DLNFibre.Core.Dimension

/-! ## The catenary `≤` direction and the one-variable polynomial tower -/

/-- **Catenary `≤` half.** For a prime point `p` of `Spec k[x₁,…,xₙ]`,
`height p + coheight p ≤ n`: a chain below `p` spliced with a chain above `p` is a chain in
`Spec R`, whose dimension is `n`. (Order level, on the spectrum point.) -/
theorem height_add_coheight_le
    (k : Type*) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    (Order.height p : ℕ∞) + Order.coheight p ≤ (n : ℕ∞) := by
  have hk : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = (n : WithBot ℕ∞) :=
    ringKrullDim_mvPolynomial_fin_field k n
  have hsup : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k))
      = ((⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k),
          Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) :=
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
  have hmem : (Order.height p + Order.coheight p : ℕ∞)
      ≤ ⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k), Order.height a + Order.coheight a :=
    le_iSup (fun a ↦ Order.height a + Order.coheight a) p
  have hcoe : ((⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k),
        Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
    hsup ▸ hk
  calc (Order.height p + Order.coheight p : ℕ∞)
      ≤ ⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k), Order.height a + Order.coheight a := hmem
    _ = (n : ℕ∞) := by exact_mod_cast hcoe

/-- **Catenary `≤` half, ideal form.** For a prime `p` of `R = k[x₁,…,xₙ]`,
`Ideal.primeHeight p + dim (R ⧸ p) ≤ n`. -/
theorem primeHeight_add_ringKrullDim_quotient_le
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (Ideal.primeHeight p : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
      ≤ (n : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient_eq_coheight ⟨p, ‹_›⟩]
  have h := height_add_coheight_le k n ⟨p, ‹_›⟩
  rw [Ideal.primeHeight]
  exact_mod_cast h

/-- **Additive height law on the one-variable tower** ([Stacks, Tag 00ON]). For `A` Noetherian and a
prime `P` of `A[X]` lying over `q = P.under A`,
`height P = height q + height (image of P in (A ⧸ q)[X])`. The extension `A → A[X]` is free hence
flat, so it satisfies going-down (`Algebra.HasGoingDown.of_flat`), and the equality is
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`. This is the load-bearing additive half of
the catenary content for polynomial rings — the brick the peel step uses. It is more general than
the field theorem (any Noetherian `A`), but it is exactly the catenary infrastructure the `≥`
induction consumes. -/
theorem height_eq_height_under_add_height_map_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : Ideal (Polynomial A)) [P.IsPrime] :
    P.height = (P.under A).height +
      (P.map (Ideal.Quotient.mk ((P.under A).map (algebraMap A (Polynomial A))))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under A) P

/-! ## Provenance of the monic-positioning substitution

The construction in this section is **copied verbatim** from
`Mathlib.RingTheory.NoetherNormalization` (`@[stacks 00OW]`, Brasca–Su–Lin–Su): the substitution
`T1`/`T` and its degree bookkeeping
(`lt_up`, `sum_r_mul_ne`, `degreeOf_zero_t`, `degreeOf_t_ne_of_ne`, `leadingCoeff_finSuccEquiv_t`,
`T_leadingcoeff_isUnit`). The **only** change is visibility: the Mathlib originals are `private`, so
they are not importable, and the public Noether-normalization API
(`exists_integral_inj_algHom_of_quotient`) exposes the *quotient* normalization but **not** the
one-variable monic-positioning automorphism that the catenary `≥`-induction needs. We re-expose the
machinery here (in the `MonicPositioning` namespace) and read off the single public consequence
`exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`. -/

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

namespace MonicPositioning

/-- `up` is `2 + f.totalDegree`; any large enough number works. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- The algebra map `Xᵢ ↦ Xᵢ + c • X₀ ^ rᵢ` for `i ≠ 0`, `X₀ ↦ X₀`. -/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

private lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/-- `T1 f 1` and its negation assemble into an algebra automorphism `T f`. -/
noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

private lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using h

private lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/-- `T` maps different monomials of `f` to polynomials with different degrees in `X₀`. -/
private lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv, degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

private lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/-- `T` maps `f` to a polynomial in `X₀` whose `X₀`-leading coefficient is a unit. -/
private lemma T_leadingcoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end MonicPositioning

/-- **Monic-coordinate positioning** ([Stacks, Tag 00OX]). For a nonzero
`f : MvPolynomial (Fin (n+1)) k` over any field `k`, there is a `k`-algebra automorphism `ψ` of
`MvPolynomial (Fin (n+1)) k` such that the image of `ψ f` under `finSuccEquiv k n` (the isomorphism
isolating variable `0`) has a **unit leading coefficient** in `X₀` — i.e. up to a unit scalar, `ψ f`
is monic in `X₀` over `k[x₁,…,xₙ]`. Characteristic- and field-cardinality-free. -/
theorem exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit (fne : f ≠ 0) :
    ∃ ψ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      IsUnit (finSuccEquiv k n (ψ f)).leadingCoeff :=
  ⟨MonicPositioning.T f, MonicPositioning.T_leadingcoeff_isUnit f fne⟩

/-! ## Dimension preservation under a monic peel -/

/-- An ideal of `A[X]` containing an element with unit leading coefficient contains a monic. -/
theorem exists_monic_mem_of_isUnit_leadingCoeff_mem {A : Type*} [CommRing A]
    {I : Ideal (Polynomial A)} {g : Polynomial A} (hg : g ∈ I) (h : IsUnit g.leadingCoeff) :
    ∃ g' ∈ I, g'.Monic :=
  ⟨h.unit⁻¹ • g, Submodule.smul_of_tower_mem _ _ hg, monic_of_isUnit_leadingCoeff_inv_smul h⟩

/-- **Quotient dimension is preserved by a monic peel.** If an ideal `P` of `A[X]` contains a monic
polynomial, then `A[X] ⧸ P` is integral over `A ⧸ (P.under A)` via an injective map, so the two
quotients have the same Krull dimension. -/
theorem ringKrullDim_quotient_eq_under_of_monic {A : Type*} [CommRing A]
    (P : Ideal (Polynomial A)) {g : Polynomial A} (mon : g.Monic) (hg : g ∈ P) :
    ringKrullDim (Polynomial A ⧸ P) = ringKrullDim (A ⧸ P.under A) := by
  have hint : (Ideal.quotientMap P (algebraMap A (Polynomial A)) le_rfl).IsIntegral := by
    rw [isIntegral_quotientMap_iff]
    exact mon.quotient_isIntegral hg
  exact ringKrullDim_eq_of_integral_injective hint Ideal.quotientMap_injective

/-! ## The fiber over the contracted prime has height at least one -/

/-- **Fiber height at least one.** If a prime `P` of `A[X]` (`q = P.under A`) contains a monic
polynomial `g`, then the fiber ideal in `A[X] ⧸ (q · A[X])` is a nonzero prime, hence has height
`≥ 1`: the monic `g` has leading coefficient `1 ∉ q`, so `g ∉ q·A[X] = ker (mk)`, so its image lies
in `P̄` and is nonzero. -/
theorem one_le_height_map_quotient_of_monic {A : Type*} [CommRing A]
    (P : Ideal (Polynomial A)) [P.IsPrime] {g : Polynomial A} (mon : g.Monic) (hg : g ∈ P) :
    1 ≤ (P.map (Ideal.Quotient.mk
      ((P.under A).map (algebraMap A (Polynomial A))))).height := by
  set J : Ideal (Polynomial A) := (P.under A).map (algebraMap A (Polynomial A)) with hJ
  -- `q = P.under A` is prime, and `J = q · A[X] ≤ P`.
  have hqP : (P.under A) = P.comap (algebraMap A (Polynomial A)) := Ideal.under_def A P
  have hJP : J ≤ P := by
    rw [hJ, hqP]; exact Ideal.map_comap_le
  haveI : (P.under A).IsPrime := inferInstance
  -- `g ∉ J`: its leading coefficient is `1 ∉ q`.
  have hgJ : g ∉ J := by
    rw [hJ, Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
    intro hall
    have : (1 : A) ∈ P.under A := by
      have := hall g.natDegree
      rwa [mon.coeff_natDegree] at this
    exact (Ideal.IsPrime.ne_top ‹(P.under A).IsPrime›)
      (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  -- The fiber `F = P.map (mk J)` is a nonzero prime in the domain `A[X] ⧸ J`.
  haveI hFprime : (P.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hJP
  have hFne : (P.map (Ideal.Quotient.mk J)) ≠ ⊥ := by
    intro hbot
    have hmem : (Ideal.Quotient.mk J) g ∈ P.map (Ideal.Quotient.mk J) :=
      Ideal.mem_map_of_mem _ hg
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hgJ hmem
  haveI hJprime : J.IsPrime := by rw [hJ, Polynomial.algebraMap_eq]; infer_instance
  haveI : Nontrivial (Polynomial A ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top hJprime)
  haveI : IsDomain (Polynomial A ⧸ J) := Ideal.Quotient.isDomain J
  -- `⊥ < F` with `⊥` of height `0` gives `1 ≤ F.height`.
  have hlt : (⊥ : Ideal (Polynomial A ⧸ J)) < P.map (Ideal.Quotient.mk J) :=
    bot_lt_iff_ne_bot.mpr hFne
  have hone : (⊥ : Ideal (Polynomial A ⧸ J)).primeHeight + 1
      ≤ (P.map (Ideal.Quotient.mk J)).primeHeight :=
    Ideal.primeHeight_add_one_le_of_lt hlt
  rw [Ideal.height_eq_primeHeight]
  have hb0 : (⊥ : Ideal (Polynomial A ⧸ J)).primeHeight = 0 := by
    rw [← Ideal.height_eq_primeHeight]; exact Ideal.height_bot
  rw [hb0, zero_add] at hone
  exact hone

/-! ## Transfer height and quotient dimension across a `k`-algebra equivalence -/

/-- A `k`-algebra equivalence preserves the height of a prime. -/
theorem height_map_algEquiv {R S : Type*} [CommRing R] [CommRing S] {k : Type*} [CommRing k]
    [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S) (p : Ideal R) :
    (p.map (e : R →+* S)).height = p.height := by
  have : p.map (e : R →+* S) = p.map (e.toRingEquiv : R ≃+* S) := rfl
  rw [this, RingEquiv.height_map]

/-- A `k`-algebra equivalence preserves the Krull dimension of the quotient by a prime. -/
theorem ringKrullDim_quotient_map_algEquiv {R S : Type*} [CommRing R] [CommRing S] {k : Type*}
    [CommRing k] [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S) (p : Ideal R) :
    ringKrullDim (S ⧸ p.map (e : R →+* S)) = ringKrullDim (R ⧸ p) :=
  ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquivAlg p (p.map (e : R →+* S)) e rfl).symm.toRingEquiv

/-! ## The catenary `≥` direction and the full equality -/

open scoped Polynomial in
/-- Induction core for the catenary `≥` direction: for every prime `p` of `k[x₁,…,xₙ]`,
`n ≤ height p + coheight p`. Inducts on `n`, peeling variable `0` after the monic positioning. -/
theorem nat_le_height_add_coheight (k : Type*) [Field k] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (n : ℕ∞) ≤ p.height + Order.coheight (⟨p, ‹_›⟩ : PrimeSpectrum (MvPolynomial (Fin n) k)) := by
  induction n with
  | zero => simp
  | succ d hd =>
    by_cases hbot : p = ⊥
    · -- `coheight ⊥ = krullDim (Spec R) = dim R = d+1`, so the bound holds with `height ≥ 0`.
      subst hbot
      have hpt : (⟨(⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)), ‹_›⟩ :
          PrimeSpectrum (MvPolynomial (Fin (d + 1)) k))
          = (⊥ : PrimeSpectrum (MvPolynomial (Fin (d + 1)) k)) := rfl
      have hcoeq : (Order.coheight (⟨(⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)), ‹_›⟩ :
          PrimeSpectrum (MvPolynomial (Fin (d + 1)) k)) : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := by
        rw [hpt, ← WithBot.coe_inj, Order.coheight_bot_eq_krullDim]
        exact ringKrullDim_mvPolynomial_fin_field k (d + 1)
      calc ((d + 1 : ℕ) : ℕ∞)
          = Order.coheight (⟨(⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)), ‹_›⟩ :
            PrimeSpectrum (MvPolynomial (Fin (d + 1)) k)) := hcoeq.symm
        _ ≤ (⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)).height + Order.coheight _ := le_add_self
    · -- Pick a nonzero `f ∈ p`, position it monic, peel variable `0`.
      obtain ⟨f, hfp, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨phi, hphi⟩ := exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit f hfne
      set Φ : MvPolynomial (Fin (d + 1)) k ≃ₐ[k] (MvPolynomial (Fin d) k)[X] :=
        phi.trans (MvPolynomial.finSuccEquiv k d) with hΦ
      set P : Ideal ((MvPolynomial (Fin d) k)[X]) := p.map (Φ : _ →+* _) with hP
      haveI : P.IsPrime := by rw [hP]; exact Ideal.map_isPrime_of_equiv Φ
      -- `P` contains the monic positioning of `f`.
      have hΦf : Φ f = MvPolynomial.finSuccEquiv k d (phi f) := rfl
      obtain ⟨g, hgP, hgmon⟩ : ∃ g ∈ P, g.Monic := by
        refine exists_monic_mem_of_isUnit_leadingCoeff_mem (g := Φ f) ?_ (hΦf ▸ hphi)
        rw [hP]; exact Ideal.mem_map_of_mem _ hfp
      -- Transfer height and quotient dim from `p` to `P`.
      have hheight : p.height = P.height := (height_map_algEquiv Φ p).symm
      have hdimP : ringKrullDim (MvPolynomial (Fin (d + 1)) k ⧸ p)
          = ringKrullDim ((MvPolynomial (Fin d) k)[X] ⧸ P) :=
        (ringKrullDim_quotient_map_algEquiv Φ p).symm
      -- Set `q = P.under A`; dim preservation and the additive height law.
      set q : Ideal (MvPolynomial (Fin d) k) := P.under (MvPolynomial (Fin d) k) with hq
      haveI : q.IsPrime := by rw [hq]; infer_instance
      have hdimq : ringKrullDim ((MvPolynomial (Fin d) k)[X] ⧸ P)
          = ringKrullDim (MvPolynomial (Fin d) k ⧸ q) :=
        ringKrullDim_quotient_eq_under_of_monic P hgmon hgP
      have hadd : P.height = q.height +
          (P.map (Ideal.Quotient.mk (q.map (algebraMap (MvPolynomial (Fin d) k) _)))).height :=
        height_eq_height_under_add_height_map_quotient P
      have hfib : 1 ≤ (P.map (Ideal.Quotient.mk
          (q.map (algebraMap (MvPolynomial (Fin d) k) _)))).height :=
        one_le_height_map_quotient_of_monic P hgmon hgP
      -- Convert the quotient dims to coheights (in `ℕ∞`).
      have hcoP : (Order.coheight (⟨p, ‹_›⟩ : PrimeSpectrum (MvPolynomial (Fin (d + 1)) k)) : ℕ∞)
          = (Order.coheight (⟨q, ‹_›⟩ : PrimeSpectrum (MvPolynomial (Fin d) k)) : ℕ∞) := by
        have e1 := ringKrullDim_quotient_eq_coheight
          (⟨p, ‹_›⟩ : PrimeSpectrum (MvPolynomial (Fin (d + 1)) k))
        have e2 := ringKrullDim_quotient_eq_coheight
          (⟨q, ‹_›⟩ : PrimeSpectrum (MvPolynomial (Fin d) k))
        have : (Order.coheight (⟨p, ‹_›⟩ : PrimeSpectrum (MvPolynomial (Fin (d + 1)) k)) :
            WithBot ℕ∞) = (Order.coheight (⟨q, ‹_›⟩ : PrimeSpectrum (MvPolynomial (Fin d) k)) :
            WithBot ℕ∞) := by rw [← e1, ← e2, hdimP, hdimq]
        exact_mod_cast this
      -- IH on `q` over `k[x₁,…,x_d]`.
      have hih := hd q
      -- Assemble: `d+1 ≤ (q.height + 1) + coheight q ≤ P.height + coheight q`.
      rw [hheight, hcoP]
      have hPq : q.height + 1 ≤ P.height := by rw [hadd]; gcongr
      calc ((d + 1 : ℕ) : ℕ∞)
          = (d : ℕ∞) + 1 := by push_cast; ring
        _ ≤ (q.height + Order.coheight (⟨q, ‹_›⟩ :
            PrimeSpectrum (MvPolynomial (Fin d) k))) + 1 := by gcongr
        _ = (q.height + 1) + Order.coheight (⟨q, ‹_›⟩ :
            PrimeSpectrum (MvPolynomial (Fin d) k)) := by ring
        _ ≤ P.height + Order.coheight (⟨q, ‹_›⟩ :
            PrimeSpectrum (MvPolynomial (Fin d) k)) := by gcongr

/-- **Catenary `≥` half, order form.** For a prime point `p` of `Spec k[x₁,…,xₙ]`,
`n ≤ height p + coheight p`. -/
theorem nat_le_height_add_coheight_spectrum (k : Type*) [Field k] (n : ℕ)
    (p : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    (n : ℕ∞) ≤ Order.height p + Order.coheight p := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  have h := nat_le_height_add_coheight k n p.asIdeal
  rwa [Ideal.height_eq_primeHeight, Ideal.primeHeight] at h

/-- **Catenary equality, order form** ([Stacks, Tag 00OS]). For a prime point `p` of
`Spec k[x₁,…,xₙ]`, `height p + coheight p = n`. -/
@[stacks 00OS "the order form: `height p + coheight p = n` for `Spec k[x₁,…,xₙ]`"]
theorem height_add_coheight_eq (k : Type*) [Field k] (n : ℕ)
    (p : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    (Order.height p : ℕ∞) + Order.coheight p = (n : ℕ∞) :=
  le_antisymm (height_add_coheight_le k n p) (nat_le_height_add_coheight_spectrum k n p)

/-- **Catenary equality (headline, ideal form)** ([Stacks, Tag 00OS]). For a prime `p` of
`R = k[x₁,…,xₙ]` (`k` any field), the height of `p` plus the Krull dimension of `R ⧸ p` equals `n`:
`Ideal.height p + ringKrullDim (R ⧸ p) = n`. The catenary identity for affine space — `R` is
equidimensional, so height and coheight are exactly complementary. -/
@[stacks 00OS]
theorem height_add_ringKrullDim_quotient_eq
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
      = (n : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient_eq_coheight ⟨p, ‹_›⟩, Ideal.height_eq_primeHeight, Ideal.primeHeight]
  have h := height_add_coheight_eq k n ⟨p, ‹_›⟩
  exact_mod_cast h

/-- **Catenary equality (headline, `primeHeight` form)** ([Stacks, Tag 00OS]). The companion to the
`≤` half `primeHeight_add_ringKrullDim_quotient_le`: for a prime `p` of `R = k[x₁,…,xₙ]`,
`Ideal.primeHeight p + ringKrullDim (R ⧸ p) = n`. -/
@[stacks 00OS]
theorem primeHeight_add_ringKrullDim_quotient_eq
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (Ideal.primeHeight p : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
      = (n : WithBot ℕ∞) := by
  rw [← Ideal.height_eq_primeHeight]
  exact height_add_ringKrullDim_quotient_eq k n p

/-! ## Non-vacuity witnesses -/

/-- Witness for the headline at the bottom prime of `ℚ[x,y]`: `height ⊥ + dim (R ⧸ ⊥) = 0 + 2 = 2`,
so the equality holds with a concrete nonzero target (`n = 2`), the dimension term carrying it. -/
example : ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)).height : WithBot ℕ∞)
    + ringKrullDim ((MvPolynomial (Fin 2) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)))
    = (2 : WithBot ℕ∞) := by
  have := height_add_ringKrullDim_quotient_eq ℚ 2 ⊥
  rwa [Nat.cast_ofNat] at this

/-- Witness that the headline's dimension term is genuinely nonzero: for the bottom prime,
`dim (R ⧸ ⊥) = dim R = 2`, so the recorded equality `0 + 2 = 2` pins a nonzero sum. -/
example : ringKrullDim ((MvPolynomial (Fin 2) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)))
    = (2 : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    ringKrullDim_mvPolynomial_fin_field, Nat.cast_ofNat]

/-- Witness that the **height summand carries weight** (not just the degenerate `⊥` case where it is
`0`): at a prime `p` of `R = ℚ[x,y]` of height `1`, the headline reduces to `1 + dim (R ⧸ p) = 2` —
the nonzero height `1` genuinely contributing to the sum, so `dim (R ⧸ p) = 1` (the quotient cut
down by the height). The hypothesis is satisfiable: the next witness exhibits a concrete nonzero
proper prime `(x)` (a principal, hence height-`1`, prime) at which it fires. -/
example (p : Ideal (MvPolynomial (Fin 2) ℚ)) [p.IsPrime] (hp : p.height = 1) :
    (1 : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin 2) ℚ) ⧸ p) = (2 : WithBot ℕ∞) := by
  have h := height_add_ringKrullDim_quotient_eq ℚ 2 p
  rw [hp] at h
  exact_mod_cast h

/-- The previous witness's height-`1` hypothesis is satisfiable: `(x)` is a (nonzero, proper) prime
of `ℚ[x,y]` (`MvPolynomial.X_prime`). (Its height is `1` by Krull's principal-ideal theorem; that
height computation is not carried out here.) -/
example : (Ideal.span {MvPolynomial.X 0} : Ideal (MvPolynomial (Fin 2) ℚ)).IsPrime := by
  rw [Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)]; exact MvPolynomial.X_prime

end DLNFibre.Core.Dimension
