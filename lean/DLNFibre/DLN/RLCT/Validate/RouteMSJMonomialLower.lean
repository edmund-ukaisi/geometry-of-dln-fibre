import DLNFibre.DLN.RLCT.Validate.Case222Cover
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJMonomialLower` — the S2-FREE monomial-threshold lower bound

**Thread `genm-sjbuild4`, R1-UPPER.** The **constructive** (axiom-`monomial_rlct`-FREE) lower
bound on the weighted-monomial RLCT threshold:

    ⨅_j axisRatio (h j) (k j)  ≤  monomialThreshold d k h.

This is the general-`d`, arbitrary-`(k, h)` **finiteness half** of the S2 citation `monomial_rlct`
(Aoyagi/Hironaka), proved DIRECTLY from Mathlib — the general-`Fin d` version of the `(1,1,1)`-only
`Case111Bridge.prodBox_rpow_integrableOn_iff`, whose header explicitly flags the general shape as
"Lean labour, not mathematics." Only the *value equality* and the *pole order* of `monomial_rlct`
genuinely need meromorphic continuation Lean lacks; the finiteness direction — that
`∫_{[0,1]^d} (∏_j u_j^{h_j})(∏_j u_j^{2 k_j})^{−c'}` converges for every `c'` below the per-axis
minimum `⨅_j (h_j+1)/(2 k_j)` — is elementary (per-axis one-variable `rpow` integrability + a
`Fin d` Tonelli product) and is proven here.

## What lands here

* `abs_rpow_lintegral_Ioo_lt_top` — single-axis convergence: `∫_{(0,ε)} |x|^s < ∞` for `−1 < s`
  (the finite companion of the banked `abs_rpow_lintegral_Ioo_eq_top`).
* `prod_rpow_lintegral_Ioo_box_lt_top` — the `Fin d` product convergence over the open box
  `(0,ε)^d`, all axis-exponents `> −1` (the `piFinSuccAbove` induction, `ENNReal.mul_lt_top`).
* `monomialIntegrand_lintegral_unitBox_lt_top` — the closed unit-box lintegral of the monomial
  integrand is finite below the per-axis minimum (boundary-null restrict bridge + the open-box
  product).
* `monomialIntegrand_integrableOn_of_lt_axisRatio` — the corresponding `IntegrableOn` (the element
  of the `monomialThreshold` `sSup` set).
* **`iInf_axisRatio_le_monomialThreshold`** — the headline: `⨅ axisRatio ≤ monomialThreshold`,
  via `ENNReal.le_of_forall_nnreal_lt` + `le_sSup`.

## Why this is a terminal prerequisite (fidelity)

The decorated recursion's terminal fires `RouteMSJLedger.sjLoss_terminal_lintegral_lt_top`, whose
hypothesis is `c' < monomialThreshold d (sharedDivisorExp e) h`. Discharging that S2-free from the
carrier threshold `c' < ½·minAdm(remChain)` needs (i) a lower bound
`½·minAdm(remChain) ≤ ⨅ axisRatio` (a combinatorial fact the recursion supplies, tying
`sharedDivisorExp`/`h` to `remChain`), and (ii)
`⨅ axisRatio ≤ monomialThreshold` — THIS module. It is decoupled from the recursion: pure measure
theory on the abstract chart data `(k, h)`.

S2-FREE: no `monomial_rlct`, no `cited_aoyagi_dln`. Axiom-clean `[propext, Classical.choice,
Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real
open scoped ENNReal BigOperators

/-! ## Single-axis convergence (the 1-D finite companion) -/

/-- **Single-axis convergence.** For `−1 < s`, the one-variable `rpow` integrand `|x|^s` has finite
`∫⁻` over the open interval `(0, ε)`. The finite companion of the banked
`abs_rpow_lintegral_Ioo_eq_top` (`s ≤ −1` ⟹ `⊤`); the analytic heart is Mathlib's
`intervalIntegral.integrableOn_Ioo_rpow_iff`. -/
theorem abs_rpow_lintegral_Ioo_lt_top (s ε : ℝ) (hε : 0 < ε) (hs : -1 < s) :
    ∫⁻ x in Set.Ioo (0 : ℝ) ε, ENNReal.ofReal (|x| ^ s) < ⊤ := by
  -- integrability of `x ↦ x^s` on `(0,ε)` from the Mathlib iff
  have hint : IntegrableOn (fun x : ℝ => x ^ s) (Set.Ioo (0 : ℝ) ε) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr hs
  -- nonneg a.e. on the interval (x > 0 there)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) ε)] (fun x : ℝ => x ^ s) := by
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ (fun x hx => ?_))
    exact Real.rpow_nonneg (le_of_lt hx.1) _
  have hfin : (∫⁻ x, ENNReal.ofReal (x ^ s) ∂(volume.restrict (Set.Ioo (0 : ℝ) ε))) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnn).mp hint.2
  -- rewrite `|x|^s = x^s` on the interval (x > 0)
  rw [show (∫⁻ x in Set.Ioo (0 : ℝ) ε, ENNReal.ofReal (|x| ^ s))
        = ∫⁻ x in Set.Ioo (0 : ℝ) ε, ENNReal.ofReal (x ^ s) from
      setLIntegral_congr_fun measurableSet_Ioo (fun x hx => by
        rw [abs_of_nonneg (le_of_lt hx.1)])]
  exact hfin

/-! ## The `Fin d` product convergence over the open box -/

/-- **Product-of-`rpow` open-box convergence.** On the open box `(0,ε)^d`, a product of per-axis
`rpow`s `∏_j |u_j|^{e_j}` has finite `∫⁻` as soon as EVERY axis has `e_j > −1`. The `piFinSuccAbove`
induction (`setLIntegral_prod` factoring, single-axis `abs_rpow_lintegral_Ioo_lt_top` + IH,
`ENNReal.mul_lt_top`) — the convergent mirror of the banked divergent
`prod_rpow_lintegral_Ioo_box_eq_top`. -/
theorem prod_rpow_lintegral_Ioo_box_lt_top : ∀ {d : ℕ} (ε : ℝ) (_hε : 0 < ε) (e : Fin d → ℝ)
    (_he : ∀ j, -1 < e j),
    ∫⁻ u in Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) ε),
        ENNReal.ofReal (∏ j, |u j| ^ (e j)) < ⊤
  | 0, ε, _hε, e, _he => by
      -- `Fin 0`: the product is empty `= 1`, `∫⁻ 1 = volume box = ∏ over ∅ = 1`.
      simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, setLIntegral_one]
      rw [volume_pi_pi]; simp
  | (n + 1), ε, hε, e, he => by
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
      have hpre : ee.symm ⁻¹' (Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε))
          = (Set.Ioo (0 : ℝ) ε) ×ˢ Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε) := by
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
        (Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε))
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
      have hinner : ∀ x, (∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε),
          ENNReal.ofReal (|x| ^ (e 0)) * ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k)))
          ∂(volume : Measure (Fin n → ℝ)))
          = ENNReal.ofReal (|x| ^ (e 0))
            * (∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε),
              ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k)))
                ∂(volume : Measure (Fin n → ℝ))) :=
        fun x => lintegral_const_mul _ (by apply Finset.measurable_prod; intro k _; fun_prop)
      simp only [hinner]
      rw [lintegral_mul_const _
        (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ (e 0))))]
      -- IH on the reduced box (all reduced exponents still `> −1`)
      have hIH : ∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε),
          ENNReal.ofReal (∏ k, |y k| ^ (e (Fin.succAbove 0 k))) < ⊤ :=
        prod_rpow_lintegral_Ioo_box_lt_top ε hε (fun k => e (Fin.succAbove 0 k))
          (fun k => he (Fin.succAbove 0 k))
      have hIH' : ∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε),
          ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k))) < ⊤ := by
        rw [show (fun y : Fin n → ℝ => ∏ k, ENNReal.ofReal (|y k| ^ (e (Fin.succAbove 0 k))))
            = fun y : Fin n → ℝ => ENNReal.ofReal (∏ k, |y k| ^ (e (Fin.succAbove 0 k))) from
          funext (fun y => (ENNReal.ofReal_prod_of_nonneg
            (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)).symm)]
        exact hIH
      -- single-axis factor finite
      have hax : ∫⁻ x in Set.Ioo (0 : ℝ) ε, ENNReal.ofReal (|x| ^ (e 0)) < ⊤ :=
        abs_rpow_lintegral_Ioo_lt_top (e 0) ε hε (he 0)
      exact ENNReal.mul_lt_top hax hIH'

/-! ## The boundary-null bridge (closed unit box vs open unit box) -/

/-- The closed unit box and the open unit box have the same volume (`= 1` each). Their difference
(the boundary faces) is therefore null, so the two restricted measures agree. -/
theorem restrict_unitBox_eq_open (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).restrict (unitBox d)
      = (volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) := by
  have hsub : Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1) ⊆ unitBox d :=
    Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self)
  have hvIcc : (volume : Measure (Fin d → ℝ)) (unitBox d) = 1 := by
    rw [unitBox, volume_pi_pi]; simp [Real.volume_Icc]
  have hvIoo : (volume : Measure (Fin d → ℝ))
      (Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) = 1 := by
    rw [volume_pi_pi]; simp [Real.volume_Ioo]
  have hmeasIoo : MeasurableSet (Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
  have hdiff : (volume : Measure (Fin d → ℝ)) (unitBox d \
      Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) = 0 := by
    rw [measure_diff hsub hmeasIoo.nullMeasurableSet (by rw [hvIoo]; exact ENNReal.one_ne_top),
      hvIcc, hvIoo, tsub_self]
  refine Measure.restrict_congr_set ?_
  rw [ae_eq_set]
  refine ⟨hdiff, ?_⟩
  rw [Set.diff_eq_empty.mpr hsub]; exact measure_empty

/-! ## The monomial-integrand box finiteness and its `IntegrableOn` form -/

/-- **The monomial integrand is measurable.** -/
theorem measurable_monomialIntegrand (d : ℕ) (k h : Fin d → ℕ) (c : ℝ) :
    Measurable (monomialIntegrand d k h c) := by
  unfold monomialIntegrand; fun_prop

/-- **The monomial integrand is nonnegative.** -/
theorem monomialIntegrand_nonneg' (d : ℕ) (k h : Fin d → ℕ) (c : ℝ) (u : Fin d → ℝ) :
    0 ≤ monomialIntegrand d k h c u := by
  unfold monomialIntegrand
  exact mul_nonneg (Finset.prod_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _))
    (Real.rpow_nonneg (Finset.prod_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)) _)

/-- **The monomial-integrand closed-unit-box lintegral is finite below the per-axis minimum.** If
every axis exponent `(h_j : ℝ) − 2 k_j c > −1`, the `∫⁻` of `monomialIntegrand d k h c` over the
closed unit box `[0,1]^d` is finite. Boundary-null bridge to the open box, where the integrand is
the `rpow` product (`monomialIntegrand_eq_prod_rpow`), finite by
`prod_rpow_lintegral_Ioo_box_lt_top`. -/
theorem monomialIntegrand_lintegral_unitBox_lt_top (d : ℕ) (k h : Fin d → ℕ) (c : ℝ)
    (he : ∀ j, (-1 : ℝ) < (h j : ℝ) - 2 * (k j : ℝ) * c) :
    ∫⁻ u in unitBox d, ENNReal.ofReal (monomialIntegrand d k h c u) < ⊤ := by
  rw [restrict_unitBox_eq_open d]
  -- on the open box the integrand is the `rpow` product
  have hcongr : ∀ u ∈ Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : ℝ) 1),
      ENNReal.ofReal (monomialIntegrand d k h c u)
        = ENNReal.ofReal (∏ j, |u j| ^ ((h j : ℝ) - 2 * (k j : ℝ) * c)) := by
    intro u hu
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hu
    have hupos : ∀ j, 0 < |u j| := fun j => by rw [abs_pos]; exact ne_of_gt (hu j).1
    rw [monomialIntegrand_eq_prod_rpow d k h c u hupos]
  rw [setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)) hcongr]
  exact prod_rpow_lintegral_Ioo_box_lt_top 1 one_pos
    (fun j => (h j : ℝ) - 2 * (k j : ℝ) * c) he

/-- **Per-axis exponent bound from the ratio.** `(c' : ℝ≥0∞) < axisRatio (h j) (k j)` gives the
real-exponent condition `−1 < (h j : ℝ) − 2 k_j c'` (trivial when `k_j = 0`; else from
`2 k_j c' < h_j + 1`). -/
theorem axisRatio_lt_exp {h k : ℕ} {c' : NNReal} (hlt : (c' : ℝ≥0∞) < axisRatio h k) :
    (-1 : ℝ) < (h : ℝ) - 2 * (k : ℝ) * (c' : ℝ) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero]
    linarith
  · -- k ≥ 1: `axisRatio = (h+1)/(2k)` finite; `c' < (h+1)/(2k)` ⟹ `c' · 2k < h+1`.
    unfold axisRatio at hlt
    have hkpos' : (0 : ℝ≥0∞) < (k : ℝ≥0∞) := by exact_mod_cast hkpos
    have h2kne : (2 * (k : ℝ≥0∞)) ≠ 0 := by positivity
    have h2ktop : (2 * (k : ℝ≥0∞)) ≠ ∞ := by finiteness
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl h2kne) (Or.inl h2ktop)] at hlt
    -- hlt : ↑c' * (2 * ↑k) < ↑h + 1  in ℝ≥0∞ — move to ℝ via `.toReal`
    have hfin1 : (c' : ℝ≥0∞) * (2 * (k : ℝ≥0∞)) ≠ ∞ := by finiteness
    have hfin2 : ((h : ℝ≥0∞) + 1) ≠ ∞ := by finiteness
    have hR := (ENNReal.toReal_lt_toReal hfin1 hfin2).mpr hlt
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.coe_toReal, ENNReal.toReal_one,
      ENNReal.toReal_natCast] at hR
    -- hR : (c':ℝ) * (2 * k) < h + 1 ; nlinarith ring-normalises the product
    nlinarith [hR, Nat.cast_nonneg (α := ℝ) k, c'.coe_nonneg]

/-- **The monomial integrand is `IntegrableOn` the unit box below the per-axis minimum.** The
`IntegrableOn` form of `monomialIntegrand_lintegral_unitBox_lt_top` (nonneg integrand +
measurability + finite `∫⁻`). This is the element of the `monomialThreshold` `sSup` set. -/
theorem monomialIntegrand_integrableOn_of_lt_axisRatio (d : ℕ) (k h : Fin d → ℕ) (c' : NNReal)
    (hlt : ∀ j, (c' : ℝ≥0∞) < axisRatio (h j) (k j)) :
    IntegrableOn (monomialIntegrand d k h (c' : ℝ)) (unitBox d) volume := by
  refine ⟨(measurable_monomialIntegrand d k h (c' : ℝ)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (fun u => monomialIntegrand_nonneg' d k h (c' : ℝ) u))]
  exact monomialIntegrand_lintegral_unitBox_lt_top d k h (c' : ℝ)
    (fun j => axisRatio_lt_exp (hlt j))

/-! ## The headline — the S2-free monomial-threshold lower bound -/

/-- **The S2-FREE monomial-threshold lower bound.** `⨅_j axisRatio (h j) (k j) ≤ monomialThreshold
d k h`, proved constructively (no `monomial_rlct`): for every `c' : NNReal` strictly below the
per-axis minimum, the integrand is integrable on the unit box
(`monomialIntegrand_integrableOn_of_lt_axisRatio`), so `c'` lies in the `monomialThreshold` `sSup`
set. `ENNReal.le_of_forall_nnreal_lt` + `le_sSup`. -/
theorem iInf_axisRatio_le_monomialThreshold (d : ℕ) (k h : Fin d → ℕ) :
    (⨅ j, axisRatio (h j) (k j)) ≤ monomialThreshold d k h := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr => ?_)
  have hlt : ∀ j, (r : ℝ≥0∞) < axisRatio (h j) (k j) :=
    fun j => lt_of_lt_of_le hr (iInf_le _ j)
  refine le_sSup ⟨r, rfl, ?_⟩
  exact monomialIntegrand_integrableOn_of_lt_axisRatio d k h r hlt

end DLNFibre.DLN.RLCT
