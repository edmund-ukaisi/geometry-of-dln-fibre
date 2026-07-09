import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1Cover
import DLNFibre.DLN.RLCT.Validate.Case111Bridge

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Cover` — the `(2,2,2)` cover assembly (measure half)

The `fm-2` measure half of `(2,2,2)` (#54/#76): assemble the 24-leaf resolution cover into the RLCT
value `rlctAtOn myF222 0 = 3/2`, where `myF222 = ‖A·B‖²` in the explicit `a00=0..b11=7` flat order
(the seam's `dlnLoss ∘ e222.symm`). The cover→`rlctAtOn` spine is `Foundations.S1Cover`; the
per-leaf thresholds are `Case222Value` (#68, both `= 3/2`).

This file holds the `(2,2,2)`-specific + `Skeleton`-dependent pieces: the per-leaf
`monomialThreshold` down-set (the `≥`-direction's per-leaf finiteness input), the ε-uniform monomial
box divergence (the `≤`-direction's analytic atom, fed to `rlctAtOn_le_of_box_diverges`) and — to
come — the concrete 3-deep chart cover and the final `rlctAtOn myF222 0 = 3/2`. The per-axis 1-D
`rpow` integrability tests (`abs_rpow_integrableOn_Ioo_iff` etc.) are reused from `Case111Bridge`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- **Monomial integrand down-set (`0 < c'`).** On the unit box, decreasing the threshold exponent
keeps integrability: `monomialIntegrand d k h c' ≤ monomialIntegrand d k h c''` pointwise (the base
`∏|uⱼ|^{2kⱼ} ∈ [0,1]`, so its `(−c')`-power is `≤` its `(−c'')`-power for `c' ≤ c''`). NOTE the
`0 < c'` hypothesis is load-bearing: at `c' = 0` the base-`0` factor jumps (`0^0 = 1` vs `0^{−c''} =
0`), breaking the domination — the `c' = 0` case is integrable directly (integrand `= ∏|uⱼ|^{hⱼ}`,
bounded), handled separately. -/
theorem monomialIntegrand_downset (d : ℕ) (k h : Fin d → ℕ) (c' c'' : ℝ)
    (hc' : 0 < c') (hle : c' ≤ c'')
    (hint : IntegrableOn (monomialIntegrand d k h c'') (unitBox d) volume) :
    IntegrableOn (monomialIntegrand d k h c') (unitBox d) volume := by
  have hmeas : Measurable (monomialIntegrand d k h c') := by unfold monomialIntegrand; fun_prop
  apply hint.mono' hmeas.aestronglyMeasurable
  have hms : MeasurableSet (unitBox d) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [ae_restrict_iff' hms]
  filter_upwards [] with u hu
  simp only [unitBox, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left] at hu
  set P := ∏ j, |u j| ^ (h j) with hP
  set b := ∏ j, |u j| ^ (2 * k j) with hb
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  have hb0 : 0 ≤ b := Finset.prod_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  have hb1 : b ≤ 1 := by
    rw [hb]; apply Finset.prod_le_one (fun j _ => pow_nonneg (abs_nonneg _) _)
    intro j _; apply pow_le_one₀ (abs_nonneg _); rw [abs_of_nonneg (hu j).1]; exact (hu j).2
  change |monomialIntegrand d k h c' u| ≤ monomialIntegrand d k h c'' u
  unfold monomialIntegrand
  rw [← hP, ← hb, abs_of_nonneg (mul_nonneg hP0 (Real.rpow_nonneg hb0 _))]
  apply mul_le_mul_of_nonneg_left _ hP0
  rcases eq_or_lt_of_le hb0 with hb00 | hbpos
  · rw [← hb00, Real.zero_rpow (by linarith : -c' ≠ 0), Real.zero_rpow (by linarith : -c'' ≠ 0)]
  · exact Real.rpow_le_rpow_of_exponent_ge hbpos hb1 (by linarith)

/-- **Below the monomial threshold ⟹ leaf integral finite** (`0 < c'`). For `c' < monomialThreshold
d k h`, the weighted monomial integrand is integrable on the unit box: extract a strictly-larger
admissible `d'` (`lt_sSup`) and apply the down-set. The `≥`-direction's per-leaf input (each chart
converges below its threshold). -/
theorem monomialIntegrand_integrable_of_lt (d : ℕ) (k h : Fin d → ℕ) (c' : NNReal) (hc' : 0 < c')
    (hlt : (c' : ℝ≥0∞) < monomialThreshold d k h) :
    IntegrableOn (monomialIntegrand d k h (c' : ℝ)) (unitBox d) volume := by
  unfold monomialThreshold at hlt
  obtain ⟨c, hc_mem, hc'c⟩ := lt_sSup_iff.1 hlt
  obtain ⟨d', rfl, hint⟩ := hc_mem
  have hle : (c' : ℝ) ≤ (d' : ℝ) := by exact_mod_cast (by exact_mod_cast hc'c.le : c' ≤ d')
  exact monomialIntegrand_downset d k h (c' : ℝ) (d' : ℝ) (by exact_mod_cast hc') hle hint

/-- **Unit-factor threshold-invariance (the per-leaf fidelity bridge).** A leaf's integrand factors
as `monomialIntegrand d k h c · |unit|^{−c}` (NOT a bare monomial — the residual `unit` with
`unit 0 ≠ 0` is nonconstant). On a set where `|unit| ∈ [a, b]` (`0 < a`), the bounded factor
`|unit|^{−c}` does NOT change integrability — `monomial·|unit|^{−c}` integrable ⟺ `monomial`
integrable — via `Integrable.bdd_mul` both ways (the `S1.3` `rlct_unit_invariant_aux` technique,
fixed-box form). So the leaf's `monomialThreshold` IS its actual RLCT: the load-bearing per-leaf
identification (the `(2,2,2)` analogue of the seam's coordinate identification). NOTE the equality
to a *bare* monomial is FALSE for a nonconstant unit — the invariance is the correct statement. -/
theorem integrableOn_monomial_mul_unit_iff (d : ℕ) (k h : Fin d → ℕ) (unit : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (c : ℝ) (a b : ℝ) (ha : 0 < a) (hmeas : Measurable unit)
    (hunit : ∀ᵐ u ∂(volume.restrict S), a ≤ |unit u| ∧ |unit u| ≤ b) :
    IntegrableOn (fun u => monomialIntegrand d k h c u * |unit u| ^ (-c)) S volume
      ↔ IntegrableOn (monomialIntegrand d k h c) S volume := by
  constructor
  · intro hint
    have key : IntegrableOn
        (fun u => |unit u| ^ c * (monomialIntegrand d k h c u * |unit u| ^ (-c))) S volume := by
      refine Integrable.bdd_mul (c := max (a ^ c) (b ^ c)) hint
        ((by fun_prop : Measurable (fun u => |unit u| ^ c)).aestronglyMeasurable) ?_
      filter_upwards [hunit] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rcases le_or_gt 0 c with hc | hc
      · exact le_max_of_le_right (Real.rpow_le_rpow (abs_nonneg _) hu.2 hc)
      · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos ha hu.1 hc.le)
    refine key.congr ?_
    filter_upwards [hunit] with u hu
    have hupos : (0 : ℝ) < |unit u| := lt_of_lt_of_le ha hu.1
    rw [← mul_assoc, mul_comm (|unit u| ^ c), mul_assoc, ← Real.rpow_add hupos]; simp
  · intro hint
    have key : IntegrableOn (fun u => |unit u| ^ (-c) * monomialIntegrand d k h c u) S volume := by
      refine Integrable.bdd_mul (c := max (a ^ (-c)) (b ^ (-c))) hint
        ((by fun_prop : Measurable (fun u => |unit u| ^ (-c))).aestronglyMeasurable) ?_
      filter_upwards [hunit] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rcases le_or_gt 0 (-c) with hc | hc
      · exact le_max_of_le_right (Real.rpow_le_rpow (abs_nonneg _) hu.2 hc)
      · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos ha hu.1 hc.le)
    refine key.congr ?_
    filter_upwards [] with u; rw [mul_comm]

/-! ## The ε-uniform monomial box divergence (the `≤`-direction analytic atom)

For the `≤` direction (`rlctAtOn_le_of_box_diverges`), a leaf integrand at-or-above its threshold
must have `∫⁻ = ⊤` on *every* box `[0,ε]^d`. The chain (Codex 2026-06-21, route Q2 single-axis
split): the 1-D atom `abs_rpow_lintegral_Ioo_eq_top` (divergence on `(0,ε)` for `s ≤ −1`, reusing
`Case111Bridge.abs_rpow_integrableOn_Ioo_iff`), then split one binding axis off via
`piEquivPiSubtypeProd` + Tonelli + `ENNReal.mul_top` (positive rest factor). -/

/-- **1-D `rpow` divergence (`= ⊤`).** For `s ≤ −1` the lintegral of `|x|^s` over `(0, ε)` is `⊤`
(`ε`-independent). The contrapositive of `Case111Bridge.abs_rpow_integrableOn_Ioo_iff` through the
nonneg `= ⊤ ↔ ¬Integrable` bridge (`lintegral_ofReal_ne_top_iff_integrable`). The per-axis seed of
the multivariate box divergence. -/
theorem abs_rpow_lintegral_Ioo_eq_top (s ε : ℝ) (hε : 0 < ε) (hs : s ≤ -1) :
    ∫⁻ x in Ioo (0 : ℝ) ε, ENNReal.ofReal (|x| ^ s) = ⊤ := by
  by_contra hfin
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] (fun x : ℝ => |x| ^ s) :=
    ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |x| ^ s) (volume.restrict (Ioo (0 : ℝ) ε)) :=
    (by fun_prop : Measurable (fun x : ℝ => |x| ^ s)).aestronglyMeasurable
  have hint : IntegrableOn (fun x : ℝ => |x| ^ s) (Ioo (0 : ℝ) ε) volume :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnn).1 hfin
  rw [abs_rpow_integrableOn_Ioo_iff s ε hε] at hint
  linarith

/-- **Monomial factoring on the positive orthant.** Where every `|u j| > 0`, the monomial integrand
is the product of the per-axis one-variable `rpow`s `|u j| ^ (h j − 2·k j·c)` (the exponent that
feeds the per-axis `rpow` integrability test). Valid only off the coordinate hyperplanes — on the
open box `(0,ε)^d` the integrand is positive, dodging the `0^{neg}` convention. -/
theorem monomialIntegrand_eq_prod_rpow (d : ℕ) (k h : Fin d → ℕ) (c : ℝ) (u : Fin d → ℝ)
    (hu : ∀ j, 0 < |u j|) :
    monomialIntegrand d k h c u
      = ∏ j, |u j| ^ ((h j : ℝ) - 2 * (k j : ℝ) * c) := by
  unfold monomialIntegrand
  rw [← Real.finset_prod_rpow _ _ (fun j _ => pow_nonneg (abs_nonneg _) _) (-c),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Real.rpow_natCast (|u j|) (h j), ← Real.rpow_natCast (|u j|) (2 * k j),
    ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_add (hu j)]
  congr 1; push_cast; ring

/-- **Binding axis from the threshold.** If `c'` is at-or-above the monomial threshold (`= ⨅ axisRatio`
by S2) and `c'` is finite, some axis `j₀` has `axisRatio (h j₀) (k j₀) ≤ c'` — the binding divisor.
Since `axisRatio _ 0 = ⊤ > c'`, that axis has `k j₀ ≠ 0`, and its one-variable exponent
`h j₀ − 2·k j₀·c' ≤ −1` (the divergence condition). The `≤`-direction's entry point: one diverging
factor suffices. -/
theorem exists_binding_axis (d : ℕ) (k h : Fin d → ℕ) (c' : ℝ) (hc'0 : 0 < c')
    (hc' : monomialThreshold d k h ≤ ENNReal.ofReal c') :
    ∃ j₀, k j₀ ≠ 0 ∧ (h j₀ : ℝ) - 2 * (k j₀ : ℝ) * c' ≤ -1 := by
  rw [(monomial_rlct d k h).1] at hc'
  have hlt : ENNReal.ofReal c' < ⊤ := ENNReal.ofReal_lt_top
  rw [← Finset.inf_univ_eq_iInf, Finset.inf_le_iff hlt] at hc'
  obtain ⟨j₀, -, hj₀⟩ := hc'
  -- `axisRatio (h j₀) (k j₀) ≤ ofReal c' < ⊤` forces `k j₀ ≠ 0` (else `axisRatio = ⊤`, `/0`)
  have hk0 : k j₀ ≠ 0 := by
    intro hk
    rw [axisRatio, hk] at hj₀
    rw [Nat.cast_zero, mul_zero, ENNReal.div_zero (by positivity), top_le_iff] at hj₀
    exact ENNReal.ofReal_ne_top hj₀
  refine ⟨j₀, hk0, ?_⟩
  -- convert `(h+1)/(2k) ≤ c'` (in ℝ≥0∞) to the real exponent bound `h − 2kc' ≤ −1`
  unfold axisRatio at hj₀
  have hbne0 : (2 * (k j₀ : ℝ≥0∞)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨by norm_num, by exact_mod_cast hk0⟩
  have hbnetop : (2 * (k j₀ : ℝ≥0∞)) ≠ ∞ := by finiteness
  rw [ENNReal.div_le_iff_le_mul (Or.inl hbne0) (Or.inl hbnetop)] at hj₀
  have h2k : (2 * (k j₀ : ℝ≥0∞)) = ENNReal.ofReal (2 * (k j₀ : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; congr 1
    · simp [ENNReal.ofReal_ofNat]
    · rw [ENNReal.ofReal_natCast]
  rw [h2k, ← ENNReal.ofReal_mul hc'0.le] at hj₀
  have hh1 : ((h j₀ : ℝ≥0∞) + 1) = ENNReal.ofReal ((h j₀ : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; congr 1
    · rw [ENNReal.ofReal_natCast]
    · simp
  rw [hh1, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hj₀
  nlinarith [hj₀]

/-- **Rest-factor positivity.** The lintegral of a product of per-axis `rpow`s over the open box
`(0,ε)^n` is strictly positive (the integrand is positive on the box, of positive measure). The
`ENNReal.mul_top` input for the single-axis split. -/
private theorem prod_rpow_lintegral_Ioo_box_pos {n : ℕ} (ε : ℝ) (hε : 0 < ε) (f : Fin n → ℝ) :
    0 < ∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε),
      ∏ k, ENNReal.ofReal (|y k| ^ (f k)) ∂(volume : Measure (Fin n → ℝ)) := by
  rw [setLIntegral_pos_iff (by apply Finset.measurable_prod; intro k _; fun_prop)]
  have hbox : 0 < (volume : Measure (Fin n → ℝ)) (Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) ε)) := by
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

/-- **Product-of-`rpow` box divergence (one binding axis).** On the open box `(0,ε)^{n+1}`, a product
of per-axis `rpow`s `∏_j |u_j|^{e_j}` integrates to `⊤` as soon as one axis `j₀` has `e_{j₀} ≤ −1`:
split that axis off (`piFinSuccAbove` measure-preserving), `setLIntegral_prod` factors the integral,
the binding-axis factor is `⊤` (`abs_rpow_lintegral_Ioo_eq_top`) and the rest factor is positive
(`prod_rpow_lintegral_Ioo_box_pos`), so `ENNReal.top_mul`. -/
private theorem prod_rpow_lintegral_Ioo_box_eq_top {n : ℕ} (ε : ℝ) (hε : 0 < ε)
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
  -- the integrand under `ee.symm` factors as `|x|^{e j₀} · ∏_k |y_k|^{e (j₀.succAbove k)}`
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
  -- factor the product-box integral (`setLIntegral_prod`), binding axis `⊤`, rest positive
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
  rw [abs_rpow_lintegral_Ioo_eq_top _ ε hε hj₀,
    ENNReal.top_mul (ne_of_gt (prod_rpow_lintegral_Ioo_box_pos ε hε _))]

/-- **ε-uniform monomial box divergence FROM AN EXPLICIT AXIS (the S2-free geometric core).** Given
an axis `j₀` whose one-variable exponent is `≤ −1` (`(h j₀ : ℝ) − 2 k_{j₀} c' ≤ −1`), the lintegral
of `|monomialIntegrand d k h c'|` over `[0, ε]^d` is `⊤` for *every* `ε > 0`. This is the analytic
heart of `monomialIntegrand_lintegral_box_eq_top` with the binding axis supplied directly rather than
extracted via S2 (`exists_binding_axis`), so it is **S2-FREE** (no `monomial_rlct`). Proof:
lower-bound by the open box `(0, ε)^d` (`lintegral_mono_set`), where the integrand factors as
`∏_j |u_j|^{h_j − 2 k_j c'}` (`monomialIntegrand_eq_prod_rpow`); the axis `j₀` forces `⊤`
(`prod_rpow_lintegral_Ioo_box_eq_top`). -/
theorem monomialIntegrand_lintegral_box_eq_top_of_axis (d : ℕ) (k h : Fin d → ℕ) (c' : ℝ)
    (j₀ : Fin d) (hexp : (h j₀ : ℝ) - 2 * (k j₀ : ℝ) * c' ≤ -1) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) ε),
        ENNReal.ofReal (|monomialIntegrand d k h c' u|) = ⊤ := by
  -- `d = n + 1` (nonempty: `j₀ : Fin d`)
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos j₀.pos).symm⟩
  set e : Fin (n + 1) → ℝ := fun j => (h j : ℝ) - 2 * (k j : ℝ) * c' with he
  -- divergence on the open sub-box `(0,ε)^d`, then `lintegral_mono_set` to `[0,ε]^d`
  have hsub : Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε)
      ⊆ Set.univ.pi (fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) ε) :=
    Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self)
  have hIoo : ∫⁻ u in Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε),
      ENNReal.ofReal (|monomialIntegrand (n + 1) k h c' u|) = ⊤ := by
    -- on the open box, `|monomial| = ∏ |u_j|^{e_j}` (nonneg, factored)
    have hcongr : ∀ u ∈ Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) ε),
        ENNReal.ofReal (|monomialIntegrand (n + 1) k h c' u|)
          = ENNReal.ofReal (∏ j, |u j| ^ (e j)) := by
      intro u hu
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hu
      have hupos : ∀ j, 0 < |u j| := fun j => by rw [abs_pos]; exact ne_of_gt (hu j).1
      rw [monomialIntegrand_eq_prod_rpow (n + 1) k h c' u hupos]
      rw [abs_of_nonneg (Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _))]
    rw [setLIntegral_congr_fun
      (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)) hcongr]
    exact prod_rpow_lintegral_Ioo_box_eq_top ε hε e j₀ hexp
  -- lift `⊤` from the sub-box to the full box
  exact eq_top_mono (hIoo ▸ lintegral_mono_set hsub) rfl

/-- **ε-uniform monomial box divergence (the `≤`-direction analytic atom).** For an exponent `c'`
at-or-above the monomial threshold (`monomialThreshold d k h ≤ c'`, the singular case `∃ j, k j ≠ 0`),
the lintegral of `|monomialIntegrand d k h c'|` over the box `[0, ε]^d` is `⊤` for *every* `ε > 0`.
ε-uniformity is the crux that makes the divergence neighbourhood-independent (the input to
`rlctAtOn_le_of_box_diverges`). The binding axis `j₀` (exponent `≤ −1`) is extracted via S2
(`exists_binding_axis`); the analytic core is the S2-free
`monomialIntegrand_lintegral_box_eq_top_of_axis`. -/
theorem monomialIntegrand_lintegral_box_eq_top (d : ℕ) (k h : Fin d → ℕ) (hk : ∃ j, k j ≠ 0)
    (c' : ℝ) (hc' : monomialThreshold d k h ≤ ENNReal.ofReal c') (hc'0 : 0 < c') {ε : ℝ}
    (hε : 0 < ε) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) ε),
        ENNReal.ofReal (|monomialIntegrand d k h c' u|) = ⊤ := by
  -- the binding axis (needs `d ≥ 1`, supplied by `hk`); the geometric core is S2-free
  obtain ⟨j₀, hkj₀, hexp⟩ := exists_binding_axis d k h c' hc'0 hc'
  exact monomialIntegrand_lintegral_box_eq_top_of_axis d k h c' j₀ hexp hε

end DLNFibre.DLN.RLCT
