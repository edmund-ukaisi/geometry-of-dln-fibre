import DLNFibre.Core.Aoyagi.IdealInvariance
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Meta.Cordon

/-!
# `Core.Aoyagi.MonomialRLCT` — Object C: the monomial-ideal RLCT (Newton / S2 boxed rule)

**BLUEPRINT (v3).** The RLCT of a **sum of squared monomials** against a monomial Jacobian weight.
This is Aoyagi's boxed rule S2 (worked.tex:173–189): after the resolution, the pulled-back loss is a
monomial times a unit, and `rlct = min_j (hⱼ+1)/(2kⱼ)`.

## The soundness fix (v2 defect 2): the rule is stated at its genuine hypothesis, not axis-only

v2 asserted the **axis value** `⨅ⱼ (hⱼ+1)/(2·minᵢ eᵢⱼ)` from `kⱼ = minᵢ eᵢⱼ` alone. That is FALSE
for coupled monomial families: for `b = (u₀u₁², u₀²u₁)` (`e = ![[1,2],[2,1]]`) the axis value is `1`
but the true weighted threshold is `2/3` (a coupled Newton valuation the coordinate minima miss).

The rule holds under Aoyagi's own **divisibility chain** `b₁ | b₂ | … | b_M` (`DivChain`;
worked.tex:483–488), i.e. some generator's exponent vector is pointwise-minimal. That is exactly the
**principal normal-crossing** condition: with `b_{k₀} | b_k` for all `k`, the ideal `⟨b₁,…,b_M⟩` is
principal `= ⟨b_{k₀}⟩`, so `∑ bₖ² = b_{k₀}² · (unit)` with the unit nonvanishing at `0`, and the sum
collapses to a single dominant monomial `b_{k₀}` whose axis exponents `k_d = e_{k₀ d} = minₖ e_{k d}`
DO give the threshold. The coupled counterexample is correctly **excluded** — it is not a chain
(`not_divChain_coupled_example`).

The DLN divisors have unit multiplicity `k_d ∈ {0,1}` (worked.tex:495: `∑ bᵢ²` vanishes to order 2
along each `u_{s,k}=0`), so on binding axes `k_d = 1` and `2·rlct = minⱼ (hⱼ+1)` — an integer min of
divisor exponents, which is what Object D consumes.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

/-! ## Monomials, the Jacobian weight, and the divisibility chain -/

/-- The monomial family `bₖ(u) = ∏_d u_d ^ (e k d)` of an exponent matrix `e : Fin M → Fin D → ℕ`. -/
noncomputable def monomialFam {M D : ℕ} (e : Fin M → Fin D → ℕ) : Fin M → (Fin D → ℝ) → ℝ :=
  fun k u ↦ ∏ d, (u d) ^ (e k d)

/-- The **monomial Jacobian weight** `W(u) = ∏_d |u_d| ^ (h_d)` — the absolute change-of-variables
determinant `|det Dg|` of a resolution chart in Aoyagi's normal form (worked.tex:177, 492–494). -/
def jacWeight {D : ℕ} (h : Fin D → ℕ) : (Fin D → ℝ) → ℝ :=
  fun u ↦ ∏ d, |u d| ^ (h d)

/-- **The divisibility chain / principal normal-crossing condition** (Aoyagi worked.tex:483–488):
some generator `b_{k₀}` divides every `bₖ`, i.e. `e k₀` is pointwise ≤ every `e k`. Under it the
monomial ideal `⟨b₁,…,b_M⟩` is principal (`= ⟨b_{k₀}⟩`) and the boxed axis rule applies. -/
def DivChain {M D : ℕ} (e : Fin M → Fin D → ℕ) : Prop :=
  ∃ k₀ : Fin M, ∀ k d, e k₀ d ≤ e k d

/-- The **binding axes** of an exponent vector `kexp`: the variables `u_d` it actually vanishes
along (`0 < kexp d`). Off these the germ is regular in `u_d` and contributes `+∞` to the boxed min
(excluded). -/
def bindingAxes {D : ℕ} (kexp : Fin D → ℕ) : Finset (Fin D) :=
  Finset.univ.filter (fun d ↦ 0 < kexp d)

/-- **The boxed monomial threshold** `min_{d : k_d>0} (h_d + 1)/(2 k_d)` (worked.tex:181), over the
binding axes of the dominant monomial's exponent `kexp`. Requires a binding axis to exist (the
singular regime — at a regular point the RLCT is `+∞`, out of scope). -/
noncomputable def monomialThreshold {D : ℕ} (kexp h : Fin D → ℕ)
    (hne : (bindingAxes kexp).Nonempty) : ℝ :=
  (bindingAxes kexp).inf' hne (fun d ↦ (h d + 1 : ℝ) / (2 * kexp d))

/-! ## The negative-example guard (defect 1/2): the coupled family is not a chain -/

/-- **Negative example (the v2 counterexample, guarded out).** `b = (u₀u₁², u₀²u₁)`
(`e = ![[1,2],[2,1]]`) is NOT a divisibility chain — neither exponent vector is pointwise ≤ the
other — so the axis rule of `monomialSumSq_wrlctAt_eq` does not apply to it. This matches the
verified truth that its weighted threshold is `2/3`, not the axis value `1`
(`∫ r·r²·r^(-6c) dr < ∞ ⟺ c < 2/3`). The `DivChain` hypothesis is exactly what excludes it. -/
theorem not_divChain_coupled_example :
    ¬ DivChain (M := 2) (D := 2) ![![1, 2], ![2, 1]] := by
  rintro ⟨k₀, hk₀⟩
  fin_cases k₀
  · exact absurd (hk₀ 1 1) (by decide)
  · exact absurd (hk₀ 0 0) (by decide)

/-! ## Network-free box integrability (the analytic substrate of the S2 rule)

The weighted RLCT of the dominant monomial reduces, after leaf (1), to the local integrability of the
`rpow`-product `∏_d |u_d|^(h_d − 2 c·k_d)` against Lebesgue measure near `0`. On a box neighbourhood
`(−ε, ε)^D = ball 0 ε` this is a Tonelli product of one-variable `rpow` integrals: convergent iff
every axis exponent is `> −1`, divergent as soon as one is `≤ −1`. These lemmas are network-free
measure theory (mirroring the `DLN`-side `RouteMSJMonomialLower`/`Case222Cover` proofs, which `Core`
cannot import); the only new ingredient here is the *symmetric* interval `(−ε, ε)`, since a
neighbourhood of `0` must contain negative coordinates. -/

/-- **`jacWeight` turns exponent-addition into a product** (L5 (★) sum-collapse atom, M1). -/
theorem jacWeight_add {D : ℕ} (h₁ h₂ : Fin D → ℕ) (u : Fin D → ℝ) :
    jacWeight (h₁ + h₂) u = jacWeight h₁ u * jacWeight h₂ u := by
  simp only [jacWeight]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun d _ => by rw [Pi.add_apply, pow_add])

/-- **`jacWeight` of a list-sum of exponents is the product of the per-term weights** (L5 (★)
telescoping atom, M1′; the branch's `∑ steps jexp` lands on `foldr (·+·) 0`). -/
theorem jacWeight_listSum {D : ℕ} (l : List (Fin D → ℕ)) (u : Fin D → ℝ) :
    jacWeight (l.foldr (· + ·) 0) u = (l.map (fun h => jacWeight h u)).prod := by
  induction l with
  | nil => simp [jacWeight]
  | cons a rest ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, jacWeight_add, ih]

open scoped ENNReal

namespace MonomialBox

variable {ε : ℝ}

/-- **1-D convergence on the positive interval.** `∫⁻_{(0,ε)} |x|^s < ⊤` for `−1 < s`. -/
private theorem absRpow_lintegral_Ioo_lt_top (s : ℝ) (hε : 0 < ε) (hs : -1 < s) :
    ∫⁻ x in Ioo (0 : ℝ) ε, ENNReal.ofReal (|x| ^ s) < ⊤ := by
  have hint : IntegrableOn (fun x : ℝ => x ^ s) (Ioo (0 : ℝ) ε) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr hs
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] (fun x : ℝ => x ^ s) :=
    (ae_restrict_iff' measurableSet_Ioo).mpr
      (ae_of_all _ (fun x hx => Real.rpow_nonneg (le_of_lt hx.1) _))
  have hfin : (∫⁻ x, ENNReal.ofReal (x ^ s) ∂(volume.restrict (Ioo (0 : ℝ) ε))) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnn).mp hint.2
  rw [show (∫⁻ x in Ioo (0 : ℝ) ε, ENNReal.ofReal (|x| ^ s))
        = ∫⁻ x in Ioo (0 : ℝ) ε, ENNReal.ofReal (x ^ s) from
      setLIntegral_congr_fun measurableSet_Ioo
        (fun x hx => by rw [abs_of_nonneg (le_of_lt hx.1)])]
  exact hfin

/-- **1-D divergence on the positive interval.** `∫⁻_{(0,ε)} |x|^s = ⊤` for `s ≤ −1`. -/
private theorem absRpow_lintegral_Ioo_eq_top (s : ℝ) (hε : 0 < ε) (hs : s ≤ -1) :
    ∫⁻ x in Ioo (0 : ℝ) ε, ENNReal.ofReal (|x| ^ s) = ⊤ := by
  by_contra hfin
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] (fun x : ℝ => |x| ^ s) :=
    ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |x| ^ s) (volume.restrict (Ioo (0 : ℝ) ε)) :=
    (by fun_prop : Measurable (fun x : ℝ => |x| ^ s)).aestronglyMeasurable
  have hint : IntegrableOn (fun x : ℝ => |x| ^ s) (Ioo (0 : ℝ) ε) volume :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnn).1 hfin
  have hint' : IntegrableOn (fun x : ℝ => x ^ s) (Ioo (0 : ℝ) ε) volume := by
    refine hint.congr_fun (fun x hx => ?_) measurableSet_Ioo
    rw [abs_of_nonneg (le_of_lt hx.1)]
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hε] at hint'
  linarith

/-- **Reflection.** The `rpow`-of-`abs` lintegral over `(−ε, 0)` equals that over `(0, ε)`
(negation is measure-preserving and `|−x| = |x|`). -/
private theorem absRpow_reflect (s : ℝ) :
    ∫⁻ x in Ioo (-ε) (0 : ℝ), ENNReal.ofReal (|x| ^ s)
      = ∫⁻ x in Ioo (0 : ℝ) ε, ENNReal.ofReal (|x| ^ s) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    measurableEmbedding_neg (fun x : ℝ => ENNReal.ofReal (|x| ^ s)) (Ioo (0 : ℝ) ε)
  simp only [abs_neg, neg_preimage, neg_Ioo, neg_zero] at h
  exact h

/-- **1-D convergence on the symmetric interval.** `∫⁻_{(−ε,ε)} |x|^s < ⊤` for `−1 < s`. -/
private theorem absRpow_lintegral_IooSymm_lt_top (s : ℝ) (hε : 0 < ε) (hs : -1 < s) :
    ∫⁻ x in Ioo (-ε) ε, ENNReal.ofReal (|x| ^ s) < ⊤ := by
  have hsplit : Ioo (-ε) ε = Ioo (-ε) 0 ∪ Ico 0 ε :=
    (Ioo_union_Ico_eq_Ioo (by linarith) (le_of_lt hε)).symm
  have hdisj : Disjoint (Ioo (-ε) (0 : ℝ)) (Ico 0 ε) :=
    Set.disjoint_left.mpr (fun x hx hx' => absurd hx'.1 (not_le.mpr hx.2))
  rw [hsplit, lintegral_union measurableSet_Ico hdisj]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · rw [absRpow_reflect s]; exact absRpow_lintegral_Ioo_lt_top s hε hs
  · rw [setLIntegral_congr (Ioo_ae_eq_Ico (a := (0 : ℝ)) (b := ε)).symm]
    exact absRpow_lintegral_Ioo_lt_top s hε hs

/-- **Box convergence (symmetric).** On the box `(−ε,ε)^d`, a product `∏_j |u_j|^(e_j)` has finite
`∫⁻` as soon as every per-axis lintegral (over the same interval `I`) is finite — the `piFinSuccAbove`
Tonelli induction. Stated for a general measurable per-axis set `I` so both the positive and the
symmetric interval instantiate it. -/
private theorem prodRpow_lintegral_box_lt_top {I : Set ℝ} (hI : MeasurableSet I) :
    ∀ {d : ℕ} (e : Fin d → ℝ),
      (∀ j, ∫⁻ x in I, ENNReal.ofReal (|x| ^ (e j)) < ⊤) →
      ∫⁻ u in Set.univ.pi (fun _ : Fin d => I),
          ENNReal.ofReal (∏ j, |u j| ^ (e j)) < ⊤
  | 0, _, _ => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, setLIntegral_one]
      rw [volume_pi_pi]; simp
  | (n + 1), e, hfin => by
      classical
      have hof : ∀ u : Fin (n + 1) → ℝ, ENNReal.ofReal (∏ j, |u j| ^ (e j))
          = ∏ j, ENNReal.ofReal (|u j| ^ (e j)) :=
        fun u => ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
      simp_rw [hof]
      set ee := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with hee
      have hsymapp : ∀ x (y : Fin n → ℝ), ee.symm (x, y) = Fin.insertNth 0 x y := fun x y => by
        rw [hee, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
      have hmpS : MeasurePreserving ee.symm (volume : Measure (ℝ × (Fin n → ℝ))) volume := by
        have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
        rwa [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
          Measure.volume_eq_prod _ _] at h
      have hpre : ee.symm ⁻¹' (Set.univ.pi (fun _ : Fin (n + 1) => I))
          = I ×ˢ Set.univ.pi (fun _ : Fin n => I) := by
        ext p; obtain ⟨x, y⟩ := p
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, hsymapp]
        constructor
        · intro hall
          refine ⟨?_, fun k => ?_⟩
          · have := hall 0; rwa [Fin.insertNth_apply_same] at this
          · have := hall (Fin.succAbove 0 k); rwa [Fin.insertNth_apply_succAbove] at this
        · rintro ⟨h0, hrest⟩ j
          rcases Fin.eq_self_or_eq_succAbove 0 j with rfl | ⟨k, rfl⟩
          · rwa [Fin.insertNth_apply_same]
          · rw [Fin.insertNth_apply_succAbove]; exact hrest k
      have htrans := hmpS.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
        (fun u : Fin (n + 1) → ℝ => ∏ j, ENNReal.ofReal (|u j| ^ (e j)))
        (Set.univ.pi (fun _ : Fin (n + 1) => I))
      rw [hpre] at htrans
      rw [← htrans]
      have hfac : ∀ x (y : Fin n → ℝ),
          (∏ j, ENNReal.ofReal (|ee.symm (x, y) j| ^ (e j)))
            = ENNReal.ofReal (|x| ^ (e 0))
              * ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k))) := by
        intro x y
        simp_rw [hsymapp]
        rw [Fin.prod_univ_succAbove _ 0, Fin.insertNth_apply_same]
        simp_rw [Fin.insertNth_apply_succAbove]
      simp_rw [hfac]
      rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _]
      rw [setLIntegral_prod _ (by
        apply Measurable.aemeasurable; apply Measurable.mul
        · exact (by fun_prop :
            Measurable (fun p : ℝ × (Fin n → ℝ) => ENNReal.ofReal (|p.1| ^ (e 0))))
        · apply Finset.measurable_prod; intro k _; fun_prop)]
      have hinner : ∀ x, (∫⁻ y in Set.univ.pi (fun _ : Fin n => I),
          ENNReal.ofReal (|x| ^ (e 0)) * ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k)))
          ∂(volume : Measure (Fin n → ℝ)))
          = ENNReal.ofReal (|x| ^ (e 0))
            * (∫⁻ y in Set.univ.pi (fun _ : Fin n => I),
              ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k)))
                ∂(volume : Measure (Fin n → ℝ))) :=
        fun x => lintegral_const_mul _ (by apply Finset.measurable_prod; intro k _; fun_prop)
      simp only [hinner]
      rw [lintegral_mul_const _
        (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ (e 0))))]
      have hIH : ∫⁻ y in Set.univ.pi (fun _ : Fin n => I),
          ENNReal.ofReal (∏ k, |y k| ^ (e (Fin.succAbove 0 k))) < ⊤ :=
        prodRpow_lintegral_box_lt_top hI (fun k => e (Fin.succAbove 0 k))
          (fun k => hfin (Fin.succAbove 0 k))
      have hIH' : ∫⁻ y in Set.univ.pi (fun _ : Fin n => I),
          ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k))) < ⊤ := by
        rw [show (fun y : Fin n → ℝ => ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k))))
            = fun y : Fin n → ℝ => ENNReal.ofReal (∏ k, |y k| ^ (e (Fin.succAbove 0 k))) from
          funext (fun y => (ENNReal.ofReal_prod_of_nonneg
            (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)).symm)]
        exact hIH
      exact ENNReal.mul_lt_top (hfin 0) hIH'

/-! ### The positive-orthant box divergence (one binding axis) -/

/-- **Rest-factor positivity** (positive orthant). -/
private theorem prodRpow_lintegral_Ioo_box_pos {n : ℕ} (hε : 0 < ε) (f : Fin n → ℝ) :
    0 < ∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε),
      ∏ k, ENNReal.ofReal (|y k| ^ (f k)) ∂(volume : Measure (Fin n → ℝ)) := by
  rw [setLIntegral_pos_iff (by apply Finset.measurable_prod; intro k _; fun_prop)]
  have hbox : 0 < (volume : Measure (Fin n → ℝ))
      (Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε)) := by
    rw [volume_pi_pi]
    exact CanonicallyOrderedAdd.prod_pos.mpr (fun k _ => by rw [Real.volume_Ioo]; simp [hε])
  apply lt_of_lt_of_le hbox
  apply measure_mono
  intro y hy
  refine ⟨?_, hy⟩
  simp only [Function.mem_support, ne_eq, Finset.prod_ne_zero_iff]
  intro k _
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hy
  have hpos : 0 < ENNReal.ofReal (|y k| ^ (f k)) := by
    rw [ENNReal.ofReal_pos]
    exact Real.rpow_pos_of_pos (by rw [abs_pos]; exact ne_of_gt (hy k).1) _
  exact ne_of_gt hpos

/-- **Box divergence (positive orthant).** On `(0,ε)^{n+1}`, `∏_j |u_j|^(e_j)` integrates to `⊤` as
soon as one axis `j₀` has `e_{j₀} ≤ −1`. -/
private theorem prodRpow_lintegral_Ioo_box_eq_top {n : ℕ} (hε : 0 < ε)
    (e : Fin (n + 1) → ℝ) (j₀ : Fin (n + 1)) (hj₀ : e j₀ ≤ -1) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε),
        ENNReal.ofReal (∏ j, |u j| ^ (e j)) = ⊤ := by
  classical
  have hof : ∀ u : Fin (n + 1) → ℝ, ENNReal.ofReal (∏ j, |u j| ^ (e j))
      = ∏ j, ENNReal.ofReal (|u j| ^ (e j)) :=
    fun u => ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
  simp_rw [hof]
  set ee := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j₀ with hee
  have hsymapp : ∀ x (y : Fin n → ℝ), ee.symm (x, y) = Fin.insertNth j₀ x y :=
    fun x y => by rw [hee, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  have hmpS : MeasurePreserving ee.symm (volume : Measure (ℝ × (Fin n → ℝ))) volume := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j₀).symm
    rwa [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod _ _] at h
  have hpre : ee.symm ⁻¹' (Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε))
      = (Set.Ioo (0 : ℝ) ε) ×ˢ Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε) := by
    ext p; obtain ⟨x, y⟩ := p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, hsymapp]
    constructor
    · intro hall
      exact ⟨by have := hall j₀; rwa [Fin.insertNth_apply_same] at this,
             fun k => by have := hall (j₀.succAbove k); rwa [Fin.insertNth_apply_succAbove] at this⟩
    · rintro ⟨h0, hrest⟩ j
      rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
      · rwa [Fin.insertNth_apply_same]
      · rw [Fin.insertNth_apply_succAbove]; exact hrest k
  have htrans := hmpS.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun u : Fin (n + 1) → ℝ => ∏ j, ENNReal.ofReal (|u j| ^ (e j)))
    (Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε))
  rw [hpre] at htrans
  rw [← htrans]
  have hfac : ∀ x (y : Fin n → ℝ),
      (∏ j, ENNReal.ofReal (|ee.symm (x, y) j| ^ (e j)))
        = ENNReal.ofReal (|x| ^ (e j₀))
          * ∏ k, ENNReal.ofReal (|y k| ^ (e (j₀.succAbove k))) := by
    intro x y
    rw [Fin.prod_univ_succAbove _ j₀]
    congr 1
    · rw [hsymapp, Fin.insertNth_apply_same]
    · exact Finset.prod_congr rfl (fun k _ => by rw [hsymapp, Fin.insertNth_apply_succAbove])
  simp_rw [hfac]
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
    Measure.volume_eq_prod _ _]
  rw [setLIntegral_prod _ (by
    apply Measurable.aemeasurable; apply Measurable.mul
    · exact (by fun_prop : Measurable (fun p : ℝ × (Fin n → ℝ) => ENNReal.ofReal (|p.1| ^ (e j₀))))
    · apply Finset.measurable_prod; intro k _; fun_prop)]
  have hinner : ∀ x, (∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε),
      ENNReal.ofReal (|x| ^ (e j₀)) * ∏ k, ENNReal.ofReal (|y k| ^ (e (j₀.succAbove k)))
      ∂(volume : Measure (Fin n → ℝ)))
      = ENNReal.ofReal (|x| ^ (e j₀)) * (∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε),
        ∏ k, ENNReal.ofReal (|y k| ^ (e (j₀.succAbove k))) ∂(volume : Measure (Fin n → ℝ))) :=
    fun x => lintegral_const_mul _ (by apply Finset.measurable_prod; intro k _; fun_prop)
  simp only [hinner]
  rw [lintegral_mul_const _ (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ (e j₀))))]
  rw [absRpow_lintegral_Ioo_eq_top _ hε hj₀,
    ENNReal.top_mul (ne_of_gt (prodRpow_lintegral_Ioo_box_pos hε _))]

/-! ### The symmetric box is a neighbourhood of `0`, and specialised convergence/divergence -/

/-- The sup-metric ball at `0` in `Fin D → ℝ` is the symmetric box `(−ε, ε)^D`. -/
private theorem ball_eq_boxSymm {D : ℕ} (hε : 0 < ε) :
    Metric.ball (0 : Fin D → ℝ) ε = Set.univ.pi (fun _ => Ioo (-ε) ε) := by
  ext u
  simp only [Metric.mem_ball, dist_pi_lt_iff hε, Real.dist_eq, Pi.zero_apply, sub_zero,
    Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, abs_lt]

/-- The symmetric box is a neighbourhood of `0`. -/
private theorem boxSymm_mem_nhds {D : ℕ} (hε : 0 < ε) :
    Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε) ∈ 𝓝 (0 : Fin D → ℝ) := by
  rw [← ball_eq_boxSymm hε]; exact Metric.ball_mem_nhds 0 hε

/-- Every neighbourhood of `0` contains a symmetric box. -/
private theorem exists_boxSymm_subset {D : ℕ} {s : Set (Fin D → ℝ)} (hs : s ∈ 𝓝 0) :
    ∃ ε > 0, Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε) ⊆ s := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 hs
  exact ⟨ε, hε, (ball_eq_boxSymm hε) ▸ hsub⟩

/-- **Symmetric box convergence.** All axis exponents `> −1` ⟹ finite box lintegral. -/
private theorem prodRpow_boxSymm_lt_top {D : ℕ} (hε : 0 < ε) (e : Fin D → ℝ)
    (he : ∀ j, -1 < e j) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε),
        ENNReal.ofReal (∏ j, |u j| ^ (e j)) < ⊤ :=
  prodRpow_lintegral_box_lt_top measurableSet_Ioo e
    (fun j => absRpow_lintegral_IooSymm_lt_top (e j) hε (he j))

/-- **Symmetric box divergence.** One axis exponent `≤ −1` ⟹ box lintegral `= ⊤`. -/
private theorem prodRpow_boxSymm_eq_top {D : ℕ} (hε : 0 < ε) (e : Fin D → ℝ)
    (d₀ : Fin D) (hd₀ : e d₀ ≤ -1) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε),
        ENNReal.ofReal (∏ j, |u j| ^ (e j)) = ⊤ := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, (Nat.succ_pred_eq_of_pos d₀.pos).symm⟩
  have hsub : Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε)
      ⊆ Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (-ε) ε) :=
    Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioo (by linarith) (le_refl ε))
  exact eq_top_mono (prodRpow_lintegral_Ioo_box_eq_top hε e d₀ hd₀ ▸ lintegral_mono_set hsub) rfl

end MonomialBox

/-! ## The strike-able reduction and the S2 rule (the analytic leaf) -/

/-- **STRIKE-ABLE leaf — the chain collapses the sum to a dominant monomial times a unit.** Under
`DivChain` with minimal generator `b_{k₀}`, `∑ₖ bₖ² = b_{k₀}² · U` where `U(u) = ∑ₖ (bₖ/b_{k₀})²` is
continuous with `U 0 = #{k : b_k = b_{k₀}} ≥ 1 > 0` (each `bₖ/b_{k₀}` is a monomial with nonnegative
exponents, vanishing at `0` unless `bₖ = b_{k₀}`). Polynomial bookkeeping; no new mathematics. -/
theorem exists_unit_sumSqFam_monomial {M D : ℕ} {e : Fin M → Fin D → ℕ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d) :
    ∃ U : (Fin D → ℝ) → ℝ, ContinuousAt U 0 ∧ 0 < U 0 ∧
      ∀ u, sumSqFam (monomialFam e) u = (monomialFam e k₀ u) ^ 2 * U u := by
  classical
  -- `U u = ∑ₖ (bₖ/b_{k₀})²` where `bₖ/b_{k₀} = ∏_d u_d^(e k d − e k₀ d)` (an honest monomial:
  -- the exponents are `≥ 0` by the chain). At `0` only the `k₀` term survives, giving `U 0 ≥ 1`.
  refine ⟨fun u ↦ ∑ k, (∏ d, (u d) ^ (e k d - e k₀ d)) ^ 2, ?_, ?_, ?_⟩
  · -- `U` is a polynomial, hence continuous.
    refine Continuous.continuousAt ?_
    refine continuous_finset_sum _ (fun k _ ↦ ?_)
    exact (continuous_finset_prod _ (fun d _ ↦ (continuous_apply d).pow _)).pow 2
  · -- `0 < U 0`: the `k₀` summand is `1`, all summands are `≥ 0`.
    refine Finset.sum_pos' (fun k _ ↦ sq_nonneg _) ⟨k₀, Finset.mem_univ k₀, ?_⟩
    have h1 : (∏ d, (0 : Fin D → ℝ) d ^ (e k₀ d - e k₀ d)) = 1 := by
      refine Finset.prod_eq_one (fun d _ ↦ ?_)
      rw [Nat.sub_self, pow_zero]
    rw [h1]; norm_num
  · -- the collapse identity, term by term.
    intro u
    simp only [sumSqFam, monomialFam]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [← mul_pow]
    congr 1
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun d _ ↦ ?_)
    rw [← pow_add]
    congr 1
    have := hchain k d
    omega

/-- **Object C — the monomial RLCT (S2 boxed rule; the analytic frontier leaf).** For a monomial
family whose exponents form a divisibility chain with minimal generator `b_{k₀}`, against a Jacobian
weight `W = jacWeight h · unit` with `unit` continuous and nonzero at `0`, the weighted RLCT at the
origin is the boxed threshold `min_{d : k_d>0} (h_d+1)/(2 k_d)` on the dominant monomial's exponents
`k = e k₀`. This is Aoyagi's boxed rule S2 (worked.tex:181–189) — the one analytic input the paper's
method permits citing; here it is a `@[blueprint]` frontier leaf with a TRUE statement (the
monomial-integral / Newton computation for a single normal-crossing monomial times a unit). The
`DivChain` hypothesis is load-bearing: it is what makes the axis exponents `e k₀` the genuine orders
and excludes the coupled counterexample (`not_divChain_coupled_example`).

`Measurable unit` is load-bearing: `wrlctAt` reads `IntegrableAtFilter`, which requires
`AEStronglyMeasurable`; a non-measurable `unit` continuous only at `0` would make `W` non-measurable
on every neighbourhood, collapsing `wrlctAt` to `0`. It matches the sibling `hWmeas` in
`IdealInvariance` and holds trivially for the resolution charts (`unit ≡ 1` per chart). -/
theorem monomialSumSq_wrlctAt_eq {M D : ℕ} {e : Fin M → Fin D → ℕ} {h : Fin D → ℕ}
    {W unit : (Fin D → ℝ) → ℝ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d)
    (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit : ContinuousAt unit 0) (hunit0 : unit 0 ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), W u = jacWeight h u * unit u) :
    wrlctAt W (sumSqFam (monomialFam e)) 0 = monomialThreshold (e k₀) h hbind := by
  -- map: C-monomial-rule (S2 boxed monomial RLCT under principal normal crossing; worked.tex:181-189)
  classical
  obtain ⟨U, hUcont, hU0, hUeq⟩ := exists_unit_sumSqFam_monomial hchain
  set K := sumSqFam (monomialFam e) with hKdef
  set T := monomialThreshold (e k₀) h hbind with hTdef
  set ev : ℝ → Fin D → ℝ := fun c d => (h d : ℝ) - 2 * (e k₀ d : ℝ) * c with hev
  -- `K` is a polynomial, hence measurable; the value germ near `0` is (leaf 1) `b_{k₀}²·U`.
  have hKmeas : Measurable K := by rw [hKdef]; unfold sumSqFam monomialFam; fun_prop
  have hUpos : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), 0 < U u := hUcont.eventually (eventually_gt_nhds hU0)
  have hmembind : ∀ d, d ∈ bindingAxes (e k₀) ↔ 0 < e k₀ d := fun d => by simp [bindingAxes]
  -- axes are null, so the germ factors into a pure `rpow`-product a.e.
  have hnull : ∀ d : Fin D, volume {u : Fin D → ℝ | u d = 0} = 0 := by
    intro d
    have hset : {u : Fin D → ℝ | u d = 0}
        = Set.univ.pi (fun i => if i = d then ({0} : Set ℝ) else Set.univ) := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hud i; split_ifs with hi
        · rw [hi]; exact hud
        · trivial
      · intro hall; have := hall d; simpa using this
    rw [hset, volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp)
  have hae_nonzero : ∀ᵐ u : Fin D → ℝ ∂volume, ∀ d, u d ≠ 0 := by
    rw [ae_all_iff]; intro d; rw [ae_iff]; simpa using hnull d
  -- `0 < T`
  have hTpos : 0 < T := by
    rw [hTdef]; unfold monomialThreshold; rw [Finset.lt_inf'_iff]
    intro d hd
    have hd' : 0 < e k₀ d := (hmembind d).mp hd
    have : (0 : ℝ) < (e k₀ d : ℝ) := by exact_mod_cast hd'
    positivity
  -- `(∀ d, −1 < ev c d) ↔ c < T`
  have hexp_iff : ∀ c : ℝ, ((∀ d, -1 < ev c d) ↔ c < T) := by
    intro c
    rw [hTdef]; unfold monomialThreshold; rw [Finset.lt_inf'_iff]
    constructor
    · intro hall d hd
      have hd' : 0 < e k₀ d := (hmembind d).mp hd
      have hev0 : (0 : ℝ) < 2 * (e k₀ d : ℝ) := by
        have : (0 : ℝ) < (e k₀ d : ℝ) := by exact_mod_cast hd'
        linarith
      have := hall d
      simp only [hev] at this
      rw [lt_div_iff₀ hev0]; nlinarith [this]
    · intro hall d
      by_cases hd : d ∈ bindingAxes (e k₀)
      · have hd' : 0 < e k₀ d := (hmembind d).mp hd
        have hev0 : (0 : ℝ) < 2 * (e k₀ d : ℝ) := by
          have : (0 : ℝ) < (e k₀ d : ℝ) := by exact_mod_cast hd'
          linarith
        have := hall d hd
        rw [lt_div_iff₀ hev0] at this
        simp only [hev]; nlinarith [this]
      · have h0 : e k₀ d = 0 := by
          by_contra hne; exact hd ((hmembind d).mpr (Nat.pos_of_ne_zero hne))
        simp only [hev, h0, Nat.cast_zero, mul_zero, zero_mul, sub_zero]
        have : (0 : ℝ) ≤ (h d : ℝ) := Nat.cast_nonneg _
        linarith
  -- the analytic heart: for `0 ≤ c`, weighted integrability near `0` ↔ every axis exponent `> −1`.
  have hkey : ∀ c : ℝ, 0 ≤ c →
      (IntegrableAtFilter (fun u => W u * negPow K c u) (𝓝 0) ↔ (∀ d, -1 < ev c d)) := by
    intro c _hc0
    -- the nuisance factor `V = unit·U^(-c)`: continuous and nonzero at `0`.
    have hVcont : ContinuousAt (fun u => unit u * (U u) ^ (-c)) 0 :=
      hunit.mul ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hU0))).comp hUcont)
    have hUcpos : (0 : ℝ) < (U 0) ^ (-c) := Real.rpow_pos_of_pos hU0 _
    have hV0abs : (0 : ℝ) < |unit 0 * (U 0) ^ (-c)| :=
      abs_pos.mpr (mul_ne_zero hunit0 (ne_of_gt hUcpos))
    have hVabs_cont : ContinuousAt (fun u => |unit u * (U u) ^ (-c)|) 0 :=
      continuous_abs.continuousAt.comp hVcont
    -- the reduced monomial germ `mono` and its measurability / nonnegativity.
    set mono : (Fin D → ℝ) → ℝ :=
      fun u => jacWeight h u * ((monomialFam e k₀ u) ^ 2) ^ (-c) with hmonodef
    have hmono_meas : Measurable mono := by
      rw [hmonodef]; simp only [jacWeight, monomialFam]; fun_prop
    have hmono_nonneg : ∀ u, 0 ≤ mono u := fun u => by
      rw [hmonodef]
      exact mul_nonneg (Finset.prod_nonneg (fun d _ => pow_nonneg (abs_nonneg _) _))
        (Real.rpow_nonneg (sq_nonneg _) _)
    -- off the axes, `mono` is the pure `rpow`-product `g c`.
    have hfactor : ∀ u : Fin D → ℝ, (∀ d, u d ≠ 0) →
        mono u = ∏ d, |u d| ^ (ev c d) := by
      intro u hu
      rw [hmonodef]; simp only [jacWeight, monomialFam, hev]
      rw [show ((∏ d, (u d) ^ (e k₀ d))) ^ 2 = ∏ d, |u d| ^ (2 * e k₀ d) from ?_]
      · rw [← Real.finset_prod_rpow _ _ (fun d _ => pow_nonneg (abs_nonneg _) _) (-c),
          ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun d _ => ?_)
        rw [← Real.rpow_natCast (|u d|) (h d), ← Real.rpow_natCast (|u d|) (2 * e k₀ d),
          ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_add (by rw [abs_pos]; exact hu d)]
        congr 1; push_cast; ring
      · rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl (fun d _ => ?_)
        rw [pow_right_comm, ← sq_abs, ← pow_mul]
    have hmono_g_ae : mono =ᵐ[volume] (fun u => ∏ d, |u d| ^ (ev c d)) := by
      filter_upwards [hae_nonzero] with u hu using hfactor u hu
    -- `∫⁻_B mono = ∫⁻_B g` on any symmetric box, so `mono`-box-finiteness ↔ box-`g`-finiteness.
    have hmono_lint_eq : ∀ ε : ℝ,
        (∫⁻ u in Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε), ENNReal.ofReal (mono u))
          = ∫⁻ u in Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε),
              ENNReal.ofReal (∏ d, |u d| ^ (ev c d)) := fun ε =>
      lintegral_congr_ae (ae_restrict_of_ae (hmono_g_ae.fun_comp ENNReal.ofReal))
    constructor
    · -- integrable ⟹ every exponent `> −1` (contrapositive via box divergence)
      intro hint
      by_contra hcon
      push_neg at hcon
      obtain ⟨d₀, hd₀⟩ := hcon
      have hd₀le : ev c d₀ ≤ -1 := hd₀
      obtain ⟨s, hs, hsint⟩ := hint
      -- lower bound `|V| > m` on a box inside `s`.
      have hhalf : |unit 0 * (U 0) ^ (-c)| / 2 < |unit 0 * (U 0) ^ (-c)| := by linarith
      have hVlb : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
          |unit 0 * (U 0) ^ (-c)| / 2 < |unit u * (U u) ^ (-c)| := by
        filter_upwards [hVabs_cont.eventually (Ioi_mem_nhds hhalf)]
          with u hu using Set.mem_Ioi.mp hu
      obtain ⟨ε, hε, hεsub⟩ :=
        MonomialBox.exists_boxSymm_subset
          (Filter.inter_mem hs (Filter.inter_mem hW (Filter.inter_mem hUpos hVlb)))
      set B := Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε) with hBdef
      have hBmeas : MeasurableSet B := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
      -- integrand is integrable on `B` (restricting from `s`).
      have hintB : IntegrableOn (fun u => W u * negPow K c u) B :=
        hsint.mono_set (fun u hu => ((hεsub hu).1))
      set m := |unit 0 * (U 0) ^ (-c)| / 2 with hmdef
      have hmpos : 0 < m := by rw [hmdef]; linarith
      -- `mono ≤ (1/m)·|integrand|` on `B`, so `mono` integrable on `B`.
      have hmono_intB : IntegrableOn mono B := by
        refine (hintB.abs.const_mul (1 / m)).mono' hmono_meas.aestronglyMeasurable ?_
        refine (ae_restrict_iff' hBmeas).mpr (ae_of_all _ (fun u hu => ?_))
        have hb := hεsub hu
        have hWu : W u = jacWeight h u * unit u := hb.2.1
        have hUu : 0 < U u := hb.2.2.1
        have hVu : m < |unit u * (U u) ^ (-c)| := hb.2.2.2
        have hival : W u * negPow K c u = mono u * (unit u * (U u) ^ (-c)) := by
          rw [hmonodef, negPow_apply, hWu, hUeq u, Real.mul_rpow (sq_nonneg _) (le_of_lt hUu)]; ring
        have h1 : mono u * m ≤ mono u * |unit u * (U u) ^ (-c)| :=
          mul_le_mul_of_nonneg_left (le_of_lt hVu) (hmono_nonneg u)
        rw [Real.norm_eq_abs, abs_of_nonneg (hmono_nonneg u), hival, abs_mul,
          abs_of_nonneg (hmono_nonneg u)]
        rw [show (1 : ℝ) / m * (mono u * |unit u * (U u) ^ (-c)|)
              = (mono u * |unit u * (U u) ^ (-c)|) / m from by ring, le_div_iff₀ hmpos]
        linarith [h1]
      -- but `∫⁻_B mono = ∫⁻_B g = ⊤` (box divergence at `d₀`) — contradiction.
      have hfin : (∫⁻ u in Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε),
          ENNReal.ofReal (mono u)) < ⊤ := by
        have h2 := hmono_intB.2
        rw [hBdef, hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun u => hmono_nonneg u))] at h2
        exact h2
      rw [hmono_lint_eq ε, MonomialBox.prodRpow_boxSymm_eq_top hε (ev c) d₀ hd₀le] at hfin
      exact absurd hfin (lt_irrefl _)
    · -- every exponent `> −1` ⟹ integrable near `0`
      intro hall
      -- upper bound `|V| < M` on a box.
      have hVub : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
          |unit u * (U u) ^ (-c)| < |unit 0 * (U 0) ^ (-c)| + 1 := by
        filter_upwards [hVabs_cont.eventually (Iio_mem_nhds (lt_add_one _))]
          with u hu using Set.mem_Iio.mp hu
      obtain ⟨ε, hε, hεsub⟩ :=
        MonomialBox.exists_boxSymm_subset (Filter.inter_mem hW (Filter.inter_mem hUpos hVub))
      set B := Set.univ.pi (fun _ : Fin D => Ioo (-ε) ε) with hBdef
      have hBmeas : MeasurableSet B := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
      set M := |unit 0 * (U 0) ^ (-c)| + 1 with hMdef
      -- `mono` integrable on `B` (box convergence, all exponents `> −1`).
      have hmono_intB : IntegrableOn mono B := by
        refine ⟨hmono_meas.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun u => hmono_nonneg u)), hBdef,
          hmono_lint_eq ε]
        exact MonomialBox.prodRpow_boxSymm_lt_top hε (ev c) hall
      -- integrand `≤ M·mono` on `B`, so integrable, so integrable at the filter.
      refine ⟨B, MonomialBox.boxSymm_mem_nhds hε, ?_⟩
      refine (hmono_intB.const_mul M).mono' ?_ ?_
      · -- a.e. strong measurability: the germ equals the measurable `jacWeight·unit·K^(-c)` on `B`
        have haem : (fun u => W u * negPow K c u)
            =ᵐ[volume.restrict B] (fun u => jacWeight h u * unit u * negPow K c u) := by
          refine (ae_restrict_iff' hBmeas).mpr (ae_of_all _ (fun u hu => ?_))
          show W u * negPow K c u = jacWeight h u * unit u * negPow K c u
          rw [(hεsub hu).1]
        refine AEStronglyMeasurable.congr ?_ haem.symm
        have hjacmeas : Measurable (fun u : Fin D → ℝ => ∏ d, |u d| ^ (h d)) := by fun_prop
        have : Measurable (fun u => jacWeight h u * unit u * negPow K c u) := by
          unfold jacWeight
          exact (hjacmeas.mul hunitmeas).mul (measurable_negPow hKmeas c)
        exact this.aestronglyMeasurable
      · -- the domination `‖integrand‖ ≤ M·mono` on `B`
        refine (ae_restrict_iff' hBmeas).mpr (ae_of_all _ (fun u hu => ?_))
        have hb := hεsub hu
        have hWu : W u = jacWeight h u * unit u := hb.1
        have hUu : 0 < U u := hb.2.1
        have hVu : |unit u * (U u) ^ (-c)| < M := hb.2.2
        have hival : W u * negPow K c u = mono u * (unit u * (U u) ^ (-c)) := by
          rw [hmonodef, negPow_apply, hWu, hUeq u, Real.mul_rpow (sq_nonneg _) (le_of_lt hUu)]; ring
        rw [Real.norm_eq_abs, hival, abs_mul, abs_of_nonneg (hmono_nonneg u)]
        calc mono u * |unit u * (U u) ^ (-c)| ≤ mono u * M :=
              mul_le_mul_of_nonneg_left (le_of_lt hVu) (hmono_nonneg u)
          _ = M * mono u := by ring
  -- read off the RLCT as `sSup (Ico 0 T) = T`.
  have hset : wLocalAdmissibleExponents W K 0 = Set.Ico 0 T := by
    ext c
    simp only [wLocalAdmissibleExponents, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨hc0, hint⟩; exact ⟨hc0, (hexp_iff c).mp ((hkey c hc0).mp hint)⟩
    · rintro ⟨hc0, hlt⟩; exact ⟨hc0, (hkey c hc0).mpr ((hexp_iff c).mpr hlt)⟩
  rw [wrlctAt, hset, csSup_Ico hTpos]

/-- **Object C, DLN normal-crossing form: `2·rlct = minⱼ (hⱼ+1)`.** When every binding divisor has
**unit multiplicity** (`e k₀ d = 1` on the binding axes — the DLN case, worked.tex:495), the boxed
threshold is `½ · min` of the integer divisor exponents `h_d + 1`, so `2·wrlctAt = ⨅ binding (h_d+1)`.
This is the integer min-of-divisor-exponents Object D bridges to `qipMin`/`cCodim`. -/
theorem monomialSumSq_two_mul_wrlctAt_eq_min {M D : ℕ} {e : Fin M → Fin D → ℕ} {h : Fin D → ℕ}
    {W unit : (Fin D → ℝ) → ℝ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d)
    (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit1 : ∀ d ∈ bindingAxes (e k₀), e k₀ d = 1)
    (hunit : ContinuousAt unit 0) (hunit0 : unit 0 ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), W u = jacWeight h u * unit u) :
    2 * wrlctAt W (sumSqFam (monomialFam e)) 0
      = ((bindingAxes (e k₀)).inf' hbind (fun d ↦ (h d + 1 : ℝ))) := by
  -- map: C-dln-unit-multiplicity (k_d = 1 ⟹ boxed min is ½·min integer divisor exponents)
  rw [monomialSumSq_wrlctAt_eq hchain hbind hunit hunit0 hunitmeas hW]
  unfold monomialThreshold
  -- `2 · min` distributes (`2 ≥ 0` is monotone), then each binding term `2·(h+1)/(2·1) = h+1`.
  have hg : ∀ x y : ℝ, 2 * (x ⊓ y) = 2 * x ⊓ 2 * y := by
    intro x y
    rcases le_total x y with hxy | hxy
    · rw [inf_of_le_left hxy, inf_of_le_left (by linarith : 2 * x ≤ 2 * y)]
    · rw [inf_of_le_right hxy, inf_of_le_right (by linarith : 2 * y ≤ 2 * x)]
  rw [Finset.comp_inf'_eq_inf'_comp hbind (fun x : ℝ => 2 * x) hg]
  refine Finset.inf'_congr hbind rfl (fun d hd => ?_)
  simp only [Function.comp_apply]
  rw [hunit1 d hd]
  push_cast
  ring

/-! ## Off-origin Object C (the per-point convergence engine for the atlas `≥` leg)

The atlas change-of-variables (`Core.Aoyagi.ProductResolution`) needs, for its `≥` (atlas-min) leg,
the local integrability of the pulled-back weighted loss **at every point of a chart's compact
domain**, not merely at the chart origin. The loss's worst singularity is at `0` (the active axes at
`p ≠ 0` are a *subset* of those at `0`), so an exponent below the *origin* threshold is admissible at
every `p`. These lemmas package that convergence half of the S2 rule **at an arbitrary base point
`p`** (the divergence half stays a `0`-phenomenon), plus the set-form of the origin rule the atlas
reads off. All additive to the landed origin case above. -/

/-- **The boxed-min inequality, arithmetic form.** Every axis exponent of the reduced monomial germ
exceeds `−1` iff `c` is below the boxed threshold: `(∀ d, -1 < h_d − 2·(e k₀ d)·c) ↔ c < T`. This is
the `hexp_iff` step of the origin rule, exposed standalone (pure `monomialThreshold`/`bindingAxes`
arithmetic — no integration): binding axes give the `(h_d+1)/(2 e_{k₀ d})` ratios, non-binding axes
(`e k₀ d = 0`) are automatically `> −1` since `h_d ≥ 0`. -/
theorem monomial_forall_neg_one_lt_iff_lt_threshold {M D : ℕ} (e : Fin M → Fin D → ℕ)
    (h : Fin D → ℕ) (k₀ : Fin M) (hbind : (bindingAxes (e k₀)).Nonempty) (c : ℝ) :
    (∀ d, -1 < (h d : ℝ) - 2 * (e k₀ d : ℝ) * c) ↔ c < monomialThreshold (e k₀) h hbind := by
  have hmembind : ∀ d, d ∈ bindingAxes (e k₀) ↔ 0 < e k₀ d := fun d => by simp [bindingAxes]
  unfold monomialThreshold
  rw [Finset.lt_inf'_iff]
  constructor
  · intro hall d hd
    have hd' : 0 < e k₀ d := (hmembind d).mp hd
    have hev0 : (0 : ℝ) < 2 * (e k₀ d : ℝ) := by
      have : (0 : ℝ) < (e k₀ d : ℝ) := by exact_mod_cast hd'
      linarith
    have := hall d
    rw [lt_div_iff₀ hev0]; nlinarith [this]
  · intro hall d
    by_cases hd : d ∈ bindingAxes (e k₀)
    · have hd' : 0 < e k₀ d := (hmembind d).mp hd
      have hev0 : (0 : ℝ) < 2 * (e k₀ d : ℝ) := by
        have : (0 : ℝ) < (e k₀ d : ℝ) := by exact_mod_cast hd'
        linarith
      have := hall d hd
      rw [lt_div_iff₀ hev0] at this
      nlinarith [this]
    · have h0 : e k₀ d = 0 := by
        by_contra hne; exact hd ((hmembind d).mpr (Nat.pos_of_ne_zero hne))
      rw [h0]; push_cast
      have : (0 : ℝ) ≤ (h d : ℝ) := Nat.cast_nonneg _
      simp only [mul_zero, zero_mul, sub_zero]; linarith

/-- **Strengthened chain-collapse unit** (`Continuous U` + `1 ≤ U`, globally). The
`exists_unit_sumSqFam_monomial` witness `U u = ∑ₖ (bₖ/b_{k₀})²` is a polynomial (hence continuous
*everywhere*, not just at `0`) and satisfies `U u ≥ 1` at *every* `u` (the `k₀` summand is the
constant `1`). The off-origin convergence engine needs `U` positive and continuous at an arbitrary
base point `p`, which these global facts supply. -/
theorem exists_unit_sumSqFam_monomial_strong {M D : ℕ} {e : Fin M → Fin D → ℕ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d) :
    ∃ U : (Fin D → ℝ) → ℝ, Continuous U ∧ (∀ u, 1 ≤ U u) ∧
      ∀ u, sumSqFam (monomialFam e) u = (monomialFam e k₀ u) ^ 2 * U u := by
  classical
  refine ⟨fun u ↦ ∑ k, (∏ d, (u d) ^ (e k d - e k₀ d)) ^ 2, ?_, ?_, ?_⟩
  · refine continuous_finset_sum _ (fun k _ ↦ ?_)
    exact (continuous_finset_prod _ (fun d _ ↦ (continuous_apply d).pow _)).pow 2
  · intro u
    -- the `k₀` summand equals `1`; the rest are `≥ 0`.
    have hk₀ : (∏ d, (u d) ^ (e k₀ d - e k₀ d)) ^ 2 = 1 := by
      have : (∏ d, (u d) ^ (e k₀ d - e k₀ d)) = 1 :=
        Finset.prod_eq_one (fun d _ ↦ by rw [Nat.sub_self, pow_zero])
      rw [this, one_pow]
    calc (1 : ℝ) = (∏ d, (u d) ^ (e k₀ d - e k₀ d)) ^ 2 := hk₀.symm
      _ ≤ ∑ k, (∏ d, (u d) ^ (e k d - e k₀ d)) ^ 2 :=
          Finset.single_le_sum (f := fun k ↦ (∏ d, (u d) ^ (e k d - e k₀ d)) ^ 2)
            (fun k _ ↦ sq_nonneg _) (Finset.mem_univ k₀)
  · intro u
    simp only [sumSqFam, monomialFam]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [← mul_pow]
    congr 1
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun d _ ↦ ?_)
    rw [← pow_add]
    congr 1
    have := hchain k d
    omega

/-- **The boxed threshold is positive.** Each binding-axis ratio `(h_d+1)/(2·(e k₀ d))` is `> 0`
(`h_d + 1 ≥ 1` and `e k₀ d ≥ 1` on binding axes), so their `inf'` is `> 0`. -/
theorem monomialThreshold_pos {D : ℕ} (kexp h : Fin D → ℕ) (hne : (bindingAxes kexp).Nonempty) :
    0 < monomialThreshold kexp h hne := by
  unfold monomialThreshold
  rw [Finset.lt_inf'_iff]
  intro d hd
  have hd' : 0 < kexp d := by simpa [bindingAxes] using hd
  have : (0 : ℝ) < (kexp d : ℝ) := by exact_mod_cast hd'
  positivity

/-- **Off-origin Object C — the per-point convergence engine.** For an exponent `c` below the
*origin* boxed threshold (encoded as `∀ d, -1 < h_d − 2·(e k₀ d)·c`, i.e. every axis exponent of the
reduced monomial germ exceeds `−1`), the weighted pulled-back loss `W · (∑ bₖ²)^(-c)` is integrable
on a neighbourhood of **any** base point `p` (not just the origin). The mechanism: the loss collapses
to `b_{k₀}²·U` (`U` continuous, `≥ 1`), so off the coordinate hyperplanes the integrand is
`V·∏_d |u_d|^{h_d − 2 c·e_{k₀ d}}` with `V = unit·U^{-c}` bounded near `p`; the pure power product is
integrable on a *large origin-centred symmetric box containing `p`* (every axis exponent `> −1`,
`prodRpow_boxSymm_lt_top`), and a ball around `p` sits inside it. This is the convergence half of the
S2 rule at an arbitrary base point — the divergence (worst-singularity) half stays a `0`-phenomenon
(`monomialSumSq_not_integrableAtFilter_of_exists_le`). `Measurable unit` is load-bearing (the
integrand's a.e.-strong-measurability, exactly as the origin rule). -/
theorem monomialSumSq_integrableAtFilter_of_lt {M D : ℕ} {e : Fin M → Fin D → ℕ} {h : Fin D → ℕ}
    {W unit : (Fin D → ℝ) → ℝ} {k₀ : Fin M} {p : Fin D → ℝ} {c : ℝ}
    (hchain : ∀ k d, e k₀ d ≤ e k d)
    (hβ : ∀ d, -1 < (h d : ℝ) - 2 * (e k₀ d : ℝ) * c)
    (hunit : ContinuousAt unit p) (hunit0 : unit p ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 p, W u = jacWeight h u * unit u) :
    IntegrableAtFilter (fun u ↦ W u * negPow (sumSqFam (monomialFam e)) c u) (𝓝 p) := by
  classical
  obtain ⟨U, hUcont, hU1, hUeq⟩ := exists_unit_sumSqFam_monomial_strong hchain
  set K := sumSqFam (monomialFam e) with hKdef
  set ev : Fin D → ℝ := fun d ↦ (h d : ℝ) - 2 * (e k₀ d : ℝ) * c with hev
  have hKmeas : Measurable K := by rw [hKdef]; unfold sumSqFam monomialFam; fun_prop
  have hUpos : ∀ u, 0 < U u := fun u ↦ lt_of_lt_of_le one_pos (hU1 u)
  have hVcont : ContinuousAt (fun u ↦ unit u * (U u) ^ (-c)) p :=
    hunit.mul ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (hUpos p)))).comp
      hUcont.continuousAt)
  have hVabs_cont : ContinuousAt (fun u ↦ |unit u * (U u) ^ (-c)|) p :=
    continuous_abs.continuousAt.comp hVcont
  set mono : (Fin D → ℝ) → ℝ :=
    fun u ↦ jacWeight h u * ((monomialFam e k₀ u) ^ 2) ^ (-c) with hmonodef
  have hmono_meas : Measurable mono := by
    rw [hmonodef]; simp only [jacWeight, monomialFam]; fun_prop
  have hmono_nonneg : ∀ u, 0 ≤ mono u := fun u ↦ by
    rw [hmonodef]
    exact mul_nonneg (Finset.prod_nonneg (fun d _ ↦ pow_nonneg (abs_nonneg _) _))
      (Real.rpow_nonneg (sq_nonneg _) _)
  -- coordinate hyperplanes are null, so `mono` factors into a pure `rpow`-product a.e.
  have hnull : ∀ d : Fin D, volume {u : Fin D → ℝ | u d = 0} = 0 := by
    intro d
    have hset : {u : Fin D → ℝ | u d = 0}
        = Set.univ.pi (fun i ↦ if i = d then ({0} : Set ℝ) else Set.univ) := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hud i; split_ifs with hi
        · rw [hi]; exact hud
        · trivial
      · intro hall; have := hall d; simpa using this
    rw [hset, volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp)
  have hae_nonzero : ∀ᵐ u : Fin D → ℝ ∂volume, ∀ d, u d ≠ 0 := by
    rw [ae_all_iff]; intro d; rw [ae_iff]; simpa using hnull d
  have hfactor : ∀ u : Fin D → ℝ, (∀ d, u d ≠ 0) → mono u = ∏ d, |u d| ^ (ev d) := by
    intro u hu
    rw [hmonodef]; simp only [jacWeight, monomialFam, hev]
    rw [show ((∏ d, (u d) ^ (e k₀ d))) ^ 2 = ∏ d, |u d| ^ (2 * e k₀ d) from ?_]
    · rw [← Real.finset_prod_rpow _ _ (fun d _ ↦ pow_nonneg (abs_nonneg _) _) (-c),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun d _ ↦ ?_)
      rw [← Real.rpow_natCast (|u d|) (h d), ← Real.rpow_natCast (|u d|) (2 * e k₀ d),
        ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_add (by rw [abs_pos]; exact hu d)]
      congr 1; push_cast; ring
    · rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl (fun d _ ↦ ?_)
      rw [pow_right_comm, ← sq_abs, ← pow_mul]
  have hmono_g_ae : mono =ᵐ[volume] (fun u ↦ ∏ d, |u d| ^ (ev d)) := by
    filter_upwards [hae_nonzero] with u hu using hfactor u hu
  -- a large origin-centred symmetric box `(−R, R)^D` containing `p`.
  set R : ℝ := (∑ d, |p d|) + 1 with hRdef
  have hR : 0 < R := by
    have : (0 : ℝ) ≤ ∑ d, |p d| := Finset.sum_nonneg (fun d _ ↦ abs_nonneg _)
    rw [hRdef]; linarith
  have hpR : ∀ d, |p d| < R := by
    intro d
    have hle : |p d| ≤ ∑ d, |p d| :=
      Finset.single_le_sum (f := fun d ↦ |p d|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ d)
    rw [hRdef]; linarith
  set box : Set (Fin D → ℝ) := Set.univ.pi (fun _ : Fin D ↦ Set.Ioo (-R) R) with hboxdef
  have hofReal_ae : (fun u ↦ ENNReal.ofReal (mono u))
      =ᵐ[volume] (fun u ↦ ENNReal.ofReal (∏ d, |u d| ^ (ev d))) :=
    hmono_g_ae.mono (fun u hu ↦ congrArg ENNReal.ofReal hu)
  have hbig : ∫⁻ u in box, ENNReal.ofReal (mono u) < ⊤ := by
    rw [hboxdef, lintegral_congr_ae (ae_restrict_of_ae hofReal_ae)]
    exact MonomialBox.prodRpow_boxSymm_lt_top hR ev hβ
  have hbox_mem : box ∈ 𝓝 p := by
    refine IsOpen.mem_nhds (isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)) ?_
    simp only [hboxdef, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    intro d
    have := hpR d; rw [abs_lt] at this; exact ⟨this.1, this.2⟩
  -- upper bound `M` for `|V|` near `p`; a ball `B ⊆ box ∩ {W-model} ∩ {|V|<M}`.
  set Mub : ℝ := |unit p * (U p) ^ (-c)| + 1 with hMubdef
  have hVub : ∀ᶠ u in 𝓝 p, |unit u * (U u) ^ (-c)| < Mub := by
    filter_upwards [hVabs_cont.eventually (Iio_mem_nhds (lt_add_one _))]
      with u hu using Set.mem_Iio.mp hu
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.1 (Filter.inter_mem hbox_mem (Filter.inter_mem hW hVub))
  set B := Metric.ball p ε with hBdef
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hmono_intB : IntegrableOn mono B := by
    refine ⟨hmono_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun u ↦ hmono_nonneg u))]
    calc ∫⁻ u in B, ENNReal.ofReal (mono u)
        ≤ ∫⁻ u in box, ENNReal.ofReal (mono u) :=
          lintegral_mono_set (fun u hu ↦ (hεsub hu).1)
      _ < ⊤ := hbig
  refine ⟨B, Metric.ball_mem_nhds p hε, ?_⟩
  refine (hmono_intB.const_mul Mub).mono' ?_ ?_
  · have haem : (fun u ↦ W u * negPow K c u)
        =ᵐ[volume.restrict B] (fun u ↦ jacWeight h u * unit u * negPow K c u) := by
      refine (ae_restrict_iff' hBmeas).mpr (ae_of_all _ (fun u hu ↦ ?_))
      show W u * negPow K c u = jacWeight h u * unit u * negPow K c u
      rw [(hεsub hu).2.1]
    refine AEStronglyMeasurable.congr ?_ haem.symm
    have hjacmeas : Measurable (fun u : Fin D → ℝ ↦ ∏ d, |u d| ^ (h d)) := by fun_prop
    have : Measurable (fun u ↦ jacWeight h u * unit u * negPow K c u) := by
      unfold jacWeight
      exact (hjacmeas.mul hunitmeas).mul (measurable_negPow hKmeas c)
    exact this.aestronglyMeasurable
  · refine (ae_restrict_iff' hBmeas).mpr (ae_of_all _ (fun u hu ↦ ?_))
    have hb := hεsub hu
    have hWu : W u = jacWeight h u * unit u := hb.2.1
    have hUu : 0 < U u := hUpos u
    have hVu : |unit u * (U u) ^ (-c)| < Mub := hb.2.2
    have hival : W u * negPow K c u = mono u * (unit u * (U u) ^ (-c)) := by
      rw [hmonodef, negPow_apply, hWu, hUeq u, Real.mul_rpow (sq_nonneg _) (le_of_lt hUu)]; ring
    rw [Real.norm_eq_abs, hival, abs_mul, abs_of_nonneg (hmono_nonneg u)]
    calc mono u * |unit u * (U u) ^ (-c)| ≤ mono u * Mub :=
          mul_le_mul_of_nonneg_left (le_of_lt hVu) (hmono_nonneg u)
      _ = Mub * mono u := by ring

/-- **Origin divergence (the worst-singularity half).** If some axis exponent of the reduced monomial
germ is `≤ −1` (`h d₀ − 2·(e k₀ d₀)·c ≤ −1`), the weighted loss `W · (∑ bₖ²)^(-c)` is **not**
integrable on any neighbourhood of the origin. The singularity along that axis is genuinely
non-integrable at `0` (box divergence, `prodRpow_boxSymm_eq_top`): any integrable neighbourhood would
force the divergent box lintegral finite. This is a `0`-phenomenon (at `p ≠ 0` an axis with `p_d ≠ 0`
is not singular), the divergence complement of `monomialSumSq_integrableAtFilter_of_lt`. -/
theorem monomialSumSq_not_integrableAtFilter_of_exists_le {M D : ℕ} {e : Fin M → Fin D → ℕ}
    {h : Fin D → ℕ} {W unit : (Fin D → ℝ) → ℝ} {k₀ : Fin M} {c : ℝ} {d₀ : Fin D}
    (hchain : ∀ k d, e k₀ d ≤ e k d)
    (hd₀ : (h d₀ : ℝ) - 2 * (e k₀ d₀ : ℝ) * c ≤ -1)
    (hunit : ContinuousAt unit 0) (hunit0 : unit 0 ≠ 0)
    (hW : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), W u = jacWeight h u * unit u) :
    ¬ IntegrableAtFilter (fun u ↦ W u * negPow (sumSqFam (monomialFam e)) c u) (𝓝 0) := by
  classical
  intro hint
  obtain ⟨U, hUcont, hU1, hUeq⟩ := exists_unit_sumSqFam_monomial_strong hchain
  set K := sumSqFam (monomialFam e) with hKdef
  set ev : Fin D → ℝ := fun d ↦ (h d : ℝ) - 2 * (e k₀ d : ℝ) * c with hev
  have hUpos : ∀ u, 0 < U u := fun u ↦ lt_of_lt_of_le one_pos (hU1 u)
  have hUpos_ev : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), 0 < U u := Filter.Eventually.of_forall hUpos
  have hVcont : ContinuousAt (fun u ↦ unit u * (U u) ^ (-c)) 0 :=
    hunit.mul ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (hUpos 0)))).comp
      hUcont.continuousAt)
  have hUcpos : (0 : ℝ) < (U 0) ^ (-c) := Real.rpow_pos_of_pos (hUpos 0) _
  have hV0abs : (0 : ℝ) < |unit 0 * (U 0) ^ (-c)| :=
    abs_pos.mpr (mul_ne_zero hunit0 (ne_of_gt hUcpos))
  have hVabs_cont : ContinuousAt (fun u ↦ |unit u * (U u) ^ (-c)|) 0 :=
    continuous_abs.continuousAt.comp hVcont
  set mono : (Fin D → ℝ) → ℝ :=
    fun u ↦ jacWeight h u * ((monomialFam e k₀ u) ^ 2) ^ (-c) with hmonodef
  have hmono_meas : Measurable mono := by
    rw [hmonodef]; simp only [jacWeight, monomialFam]; fun_prop
  have hmono_nonneg : ∀ u, 0 ≤ mono u := fun u ↦ by
    rw [hmonodef]
    exact mul_nonneg (Finset.prod_nonneg (fun d _ ↦ pow_nonneg (abs_nonneg _) _))
      (Real.rpow_nonneg (sq_nonneg _) _)
  have hnull : ∀ d : Fin D, volume {u : Fin D → ℝ | u d = 0} = 0 := by
    intro d
    have hset : {u : Fin D → ℝ | u d = 0}
        = Set.univ.pi (fun i ↦ if i = d then ({0} : Set ℝ) else Set.univ) := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hud i; split_ifs with hi
        · rw [hi]; exact hud
        · trivial
      · intro hall; have := hall d; simpa using this
    rw [hset, volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp)
  have hae_nonzero : ∀ᵐ u : Fin D → ℝ ∂volume, ∀ d, u d ≠ 0 := by
    rw [ae_all_iff]; intro d; rw [ae_iff]; simpa using hnull d
  have hfactor : ∀ u : Fin D → ℝ, (∀ d, u d ≠ 0) → mono u = ∏ d, |u d| ^ (ev d) := by
    intro u hu
    rw [hmonodef]; simp only [jacWeight, monomialFam, hev]
    rw [show ((∏ d, (u d) ^ (e k₀ d))) ^ 2 = ∏ d, |u d| ^ (2 * e k₀ d) from ?_]
    · rw [← Real.finset_prod_rpow _ _ (fun d _ ↦ pow_nonneg (abs_nonneg _) _) (-c),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun d _ ↦ ?_)
      rw [← Real.rpow_natCast (|u d|) (h d), ← Real.rpow_natCast (|u d|) (2 * e k₀ d),
        ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_add (by rw [abs_pos]; exact hu d)]
      congr 1; push_cast; ring
    · rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl (fun d _ ↦ ?_)
      rw [pow_right_comm, ← sq_abs, ← pow_mul]
  have hmono_g_ae : mono =ᵐ[volume] (fun u ↦ ∏ d, |u d| ^ (ev d)) := by
    filter_upwards [hae_nonzero] with u hu using hfactor u hu
  -- extract an integrable box; lower-bound `|V|` there; deduce `mono` integrable on the box.
  obtain ⟨s, hs, hsint⟩ := hint
  have hhalf : |unit 0 * (U 0) ^ (-c)| / 2 < |unit 0 * (U 0) ^ (-c)| := by linarith
  have hVlb : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
      |unit 0 * (U 0) ^ (-c)| / 2 < |unit u * (U u) ^ (-c)| := by
    filter_upwards [hVabs_cont.eventually (Ioi_mem_nhds hhalf)]
      with u hu using Set.mem_Ioi.mp hu
  obtain ⟨ε, hε, hεsub⟩ :=
    MonomialBox.exists_boxSymm_subset
      (Filter.inter_mem hs (Filter.inter_mem hW (Filter.inter_mem hUpos_ev hVlb)))
  set B := Set.univ.pi (fun _ : Fin D => Set.Ioo (-ε) ε) with hBdef
  have hBmeas : MeasurableSet B := MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioo)
  have hintB : IntegrableOn (fun u ↦ W u * negPow K c u) B :=
    hsint.mono_set (fun u hu ↦ (hεsub hu).1)
  set m := |unit 0 * (U 0) ^ (-c)| / 2 with hmdef
  have hmpos : 0 < m := by rw [hmdef]; linarith
  have hmono_intB : IntegrableOn mono B := by
    refine (hintB.abs.const_mul (1 / m)).mono' hmono_meas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hBmeas).mpr (ae_of_all _ (fun u hu ↦ ?_))
    have hb := hεsub hu
    have hWu : W u = jacWeight h u * unit u := hb.2.1
    have hUu : 0 < U u := hb.2.2.1
    have hVu : m < |unit u * (U u) ^ (-c)| := hb.2.2.2
    have hival : W u * negPow K c u = mono u * (unit u * (U u) ^ (-c)) := by
      rw [hmonodef, negPow_apply, hWu, hUeq u, Real.mul_rpow (sq_nonneg _) (le_of_lt hUu)]; ring
    have h1 : mono u * m ≤ mono u * |unit u * (U u) ^ (-c)| :=
      mul_le_mul_of_nonneg_left (le_of_lt hVu) (hmono_nonneg u)
    rw [Real.norm_eq_abs, abs_of_nonneg (hmono_nonneg u), hival, abs_mul,
      abs_of_nonneg (hmono_nonneg u)]
    rw [show (1 : ℝ) / m * (mono u * |unit u * (U u) ^ (-c)|)
          = (mono u * |unit u * (U u) ^ (-c)|) / m from by ring, le_div_iff₀ hmpos]
    linarith [h1]
  -- but the box lintegral of `mono` diverges (axis `d₀`), a contradiction.
  have hofReal_ae : (fun u ↦ ENNReal.ofReal (mono u))
      =ᵐ[volume] (fun u ↦ ENNReal.ofReal (∏ d, |u d| ^ (ev d))) :=
    hmono_g_ae.mono (fun u hu ↦ congrArg ENNReal.ofReal hu)
  have hfin : (∫⁻ u in B, ENNReal.ofReal (mono u)) < ⊤ := by
    have h2 := hmono_intB.2
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun u ↦ hmono_nonneg u))] at h2
    exact h2
  rw [hBdef, lintegral_congr_ae (ae_restrict_of_ae hofReal_ae),
    MonomialBox.prodRpow_boxSymm_eq_top hε ev d₀ hd₀] at hfin
  exact absurd hfin (lt_irrefl _)

/-- **Origin S2 rule, set form.** The weighted admissible-exponent set of a chain monomial-sum at the
origin is exactly `[0, T)` with `T` the boxed threshold: convergence for `c < T`
(`monomialSumSq_integrableAtFilter_of_lt` at `p = 0`) and divergence for `c ≥ T`
(`monomialSumSq_not_integrableAtFilter_of_exists_le`). The set-level strengthening of the landed
value rule `monomialSumSq_wrlctAt_eq`; it is what Object B's atlas reads off per chart (the exact
`Ico` gives `BddAbove`, `T > 0`, and the `c < T ⟺ c` admissible equivalence in one object). -/
theorem monomialSumSq_wLocalAdmissible_eq {M D : ℕ} {e : Fin M → Fin D → ℕ} {h : Fin D → ℕ}
    {W unit : (Fin D → ℝ) → ℝ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d) (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit : ContinuousAt unit 0) (hunit0 : unit 0 ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), W u = jacWeight h u * unit u) :
    wLocalAdmissibleExponents W (sumSqFam (monomialFam e)) 0
      = Set.Ico 0 (monomialThreshold (e k₀) h hbind) := by
  ext c
  simp only [wLocalAdmissibleExponents, Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · rintro ⟨hc0, hint⟩
    refine ⟨hc0, ?_⟩
    by_contra hge
    rw [not_lt] at hge
    have hnotall : ¬ (∀ d, -1 < (h d : ℝ) - 2 * (e k₀ d : ℝ) * c) := fun hall ↦
      absurd ((monomial_forall_neg_one_lt_iff_lt_threshold e h k₀ hbind c).mp hall) (not_lt.mpr hge)
    push_neg at hnotall
    obtain ⟨d₀, hd₀⟩ := hnotall
    exact monomialSumSq_not_integrableAtFilter_of_exists_le hchain hd₀ hunit hunit0 hW hint
  · rintro ⟨hc0, hlt⟩
    refine ⟨hc0, ?_⟩
    have hβ := (monomial_forall_neg_one_lt_iff_lt_threshold e h k₀ hbind c).mpr hlt
    exact monomialSumSq_integrableAtFilter_of_lt hchain hβ hunit hunit0 hunitmeas hW

/-! ## The unweighted (classical) monomial-ideal RLCT (owed-register M1) -/

/-- **Object C, classical (unweighted) form — the monomial-ideal RLCT.** The plain local RLCT
(weight `W ≡ 1`, no Jacobian weight, `h = 0`) of the sum-of-squares of a monomial family whose
exponents form a divisibility chain (dominant generator `b_{k₀}`, `hchain : e k₀ ≤ e k` pointwise)
at the origin is the boxed minimum over the dominant monomial's binding axes:
`rlctAt (∑ₖ bₖ²) 0 = min_{d : e_{k₀ d} > 0} 1 / (2 · e_{k₀ d})`
(`= monomialThreshold (e k₀) 0 hbind`). This is the classical result — the RLCT / real
log-canonical threshold of a principal monomial ideal is `min_d 1/(2·order_d)` — read off the
weighted rule `monomialSumSq_wrlctAt_eq` through `wrlctAt_one` (which identifies the weight-`1`
weighted RLCT with the unweighted `rlctAt`).

The `DivChain` hypothesis (`hchain`) is load-bearing and NOT a technical convenience: it is exactly
the **principal normal-crossing** condition making `⟨b₁,…,b_M⟩ = ⟨b_{k₀}⟩`, so the sum collapses to
the single dominant monomial `b_{k₀}` whose coordinate orders `e_{k₀ d}` ARE the Newton data.
Without it the axis reading is false — the coupled family `b = (u₀u₁², u₀²u₁)` has threshold `2/3`,
not the axis value `1` (`not_divChain_coupled_example` guards it out). `hbind` (a binding axis
exists) is the singular regime; at a regular point the RLCT is `+∞`, out of scope.

Example (single variable, `b = u²`): `rlctAt (fun u ↦ (u 0)⁴) 0 = 1/4`, since
`∫ |u|^{-4c} du` converges near `0` iff `c < 1/4` (see the kill-set `example` below). -/
theorem monomialSumSq_rlctAt_eq {M D : ℕ} {e : Fin M → Fin D → ℕ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d) (hbind : (bindingAxes (e k₀)).Nonempty) :
    rlctAt (sumSqFam (monomialFam e)) 0 = monomialThreshold (e k₀) (fun _ ↦ 0) hbind := by
  rw [← wrlctAt_one (K := sumSqFam (monomialFam e)) (x := 0)]
  exact monomialSumSq_wrlctAt_eq (W := fun _ ↦ 1) (unit := fun _ ↦ 1) (h := fun _ ↦ 0)
    hchain hbind continuousAt_const one_ne_zero measurable_const
    (Filter.Eventually.of_forall (fun u ↦ by simp [jacWeight]))

/-- Kill-set: single-variable `b = u²` (so `∑ b² = u⁴`), a one-generator chain. The classical rule
fires and pins the RLCT to the boxed threshold `monomialThreshold ![2] 0 = 1/(2·2) = 1/4`. -/
example :
    rlctAt (sumSqFam (monomialFam (![![2]] : Fin 1 → Fin 1 → ℕ))) 0
      = monomialThreshold (![![2]] (0 : Fin 1)) (fun _ ↦ 0) (by decide) :=
  monomialSumSq_rlctAt_eq (k₀ := 0) (by decide) (by decide)

/-- Kill-set: a genuine two-variable chain `b = (u₀u₁, u₀²u₁²)` (`e 0 = ![1,1] ≤ ![2,2] = e 1`
pointwise), both axes binding, `k₀ = 0`. Exercises the corollary at `D = M = 2`. -/
example :
    rlctAt (sumSqFam (monomialFam (![![1, 1], ![2, 2]] : Fin 2 → Fin 2 → ℕ))) 0
      = monomialThreshold (![![1, 1], ![2, 2]] (0 : Fin 2)) (fun _ ↦ 0) (by decide) :=
  monomialSumSq_rlctAt_eq (k₀ := 0) (by decide) (by decide)

/-! ## The boxed threshold is coordinate-relabel invariant (owed-register M13) -/

/-- **`monomialThreshold` is invariant under a coordinate relabelling.** For a permutation
`σ : Fin D ≃ Fin D`, relabelling both the exponent vector and the Jacobian weights by `σ` leaves the
boxed threshold unchanged: `monomialThreshold (kexp ∘ σ) (h ∘ σ) = monomialThreshold kexp h`. The
binding-axis `inf'` reindexes bijectively along `σ` (a binding axis `d'` of `kexp` is the image
`σ (σ.symm d')` of a binding axis of `kexp ∘ σ`, with the same ratio), so the two minima agree by
`le_antisymm` of the two `inf'_le`/`le_inf'` bounds. The threshold companion to `conjResolution`'s
chart-relabel transport (the register's M13): an outside user permuting `Fin D` coordinates now has
the invariance for the Newton threshold itself, not only for the resolution charts. It also
pre-commutes the threshold for the non-monotone-`d` leaf-level transport (owed-register O4): the
loss-side permutation transport needs the threshold side to already be relabel-invariant. -/
theorem monomialThreshold_reindex {D : ℕ} (kexp h : Fin D → ℕ) (σ : Fin D ≃ Fin D)
    (hne : (bindingAxes kexp).Nonempty) (hne' : (bindingAxes (kexp ∘ σ)).Nonempty) :
    monomialThreshold (kexp ∘ σ) (h ∘ σ) hne' = monomialThreshold kexp h hne := by
  have hmem_iff : ∀ P : Fin D → ℕ, ∀ d, d ∈ bindingAxes P ↔ 0 < P d := fun P d ↦ by
    simp [bindingAxes]
  unfold monomialThreshold
  refine le_antisymm (Finset.le_inf' _ _ (fun d' hd' ↦ ?_)) (Finset.le_inf' _ _ (fun d hd ↦ ?_))
  · have hmem : σ.symm d' ∈ bindingAxes (kexp ∘ σ) := by
      rw [hmem_iff]
      simpa [Function.comp_apply, Equiv.apply_symm_apply] using (hmem_iff kexp d').1 hd'
    exact le_trans (Finset.inf'_le _ hmem)
      (le_of_eq (by simp [Function.comp_apply, Equiv.apply_symm_apply]))
  · have hmem : σ d ∈ bindingAxes kexp := by
      rw [hmem_iff]
      simpa [Function.comp_apply] using (hmem_iff (kexp ∘ σ) d).1 hd
    exact le_trans (Finset.inf'_le _ hmem) (le_of_eq (by simp [Function.comp_apply]))

/-- Kill-set: `monomialThreshold` of `(kexp, h) = (![1,2], ![3,5])` equals that of its swap-relabel
`(![2,1], ![5,3])` — both `min(4/2, 6/4) = 3/2`, reached at the opposite axis. -/
example :
    monomialThreshold ((![1, 2] : Fin 2 → ℕ) ∘ Equiv.swap 0 1)
        ((![3, 5] : Fin 2 → ℕ) ∘ Equiv.swap 0 1) (by decide)
      = monomialThreshold (![1, 2] : Fin 2 → ℕ) ![3, 5] (by decide) :=
  monomialThreshold_reindex (![1, 2]) (![3, 5]) (Equiv.swap 0 1) (by decide) (by decide)

end DLNFibre.Core.Aoyagi
