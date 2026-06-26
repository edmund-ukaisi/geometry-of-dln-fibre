import DLNFibre.DLN.RLCT.Foundations.S1ProductMin
import DLNFibre.DLN.RLCT.Foundations.S1Additive

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1WeightedProductMin` — the OUTER weighted product-min lemma (R1)

The new Core RLCT fact the binding-R1 general per-node `hstep` needs (cert
`14-r1-design/cert-104b-two-strata-cover.md` §1a/§4(2)): after the single-pivot blow-up
`A = y₀·Â`, the true loss factors as `dlnLoss M 0 ∘ φ₁ = y₀²·core` with **Jacobian weight**
`|det J| = |y₀|^{mk−1}`, and `core = ‖Â·B‖²` does **not** involve `y₀`. So in the blow-up chart the
weighted-cover transport problem is a **product in disjoint variable groups** `{y₀} ⊔ {core coords}`
with the Jacobian weight `|y₀|^{mk−1}` riding on the `y₀` factor only.

By Fubini over the disjoint groups, the joint weighted threshold is the **min** of the two factor
thresholds (`weightedThreshold` of a separated product = min of the per-group thresholds — the same
phenomenon as the unweighted `product_min_rlct`, now with the Jacobian weight on the `X`-factor):

  `weightedThreshold (fun p => p.1² · K p.2) (fun p => |p.1|^e) {0}`
      `= min (weightedThreshold (fun y => y²) (fun y => |y|^e) {0}) (rlctAtOn K 0)`
      `= min ((e+1)/2) (rlctAtOn K 0)`           (the `y₀`-side value below; `e = mk−1`).

The `y₀`-side `weightedThreshold (y²) (|y|^e) {0} = (e+1)/2`: the integrand is
`|y²|^{−c'}·|y|^e = |y|^{e − 2c'}`, integrable on a symmetric chart iff
`e − 2c' > −1 ⇔ c' < (e+1)/2`
(`Real.rpow` integrability on intervals — exactly the `smoothBlock1D` argument with the extra weight
`|y|^e`). With `e = mk − 1` this is `mk/2`, the `D₀` exceptional-divisor ratio
`(h+1)/(2·k_mon)` with
`(k_mon, h) = (1, mk−1)`.

## Discipline / scope
This file states the lemma against the EXISTING `weightedThreshold` / `rlctAtOn` (`Rlct.lean`) — the
`ρ`-slot of `weightedThreshold` is exactly where the change-of-variables Jacobian lands (cf.
`S1Transport`, `S1G5Charts`). The generic weighted product-min `weightedProductMin_rlct` takes the
`X`-side as a hypothesis bundle (positivity + down-set extractor), mirroring `product_min_rlct`; the
concrete `y₀`-side hypotheses are then discharged from the explicit admissibility characterisation
(`weightedMono1D_admissible_iff`). The `Y`-side is discharged from `K ≠ 0 a.e.` exactly as in
`product_min_rlct_of_ne`.

Axiom-free target (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## 1. The weighted rectangle split (Fubini over disjoint groups, with the `X`-side weight) -/

variable {X Y : Type*} [MeasureSpace X] [MeasureSpace Y] [TopologicalSpace X] [TopologicalSpace Y]
    [SFinite (volume : Measure X)] [SFinite (volume : Measure Y)] [Zero X] [Zero Y]
    [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]

omit [TopologicalSpace X] [Zero X] [BorelSpace X] [SecondCountableTopology X]
    [SFinite (volume : Measure X)] in
private theorem wpm_intOn_iff_lt (f : X → ℝ) (hf : Measurable f) (hfnn : ∀ x, 0 ≤ f x) (U : Set X) :
    IntegrableOn f U volume ↔ ∫⁻ x in U, ENNReal.ofReal (f x) < ⊤ := by
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all _ hfnn)]
  simp only [hf.aestronglyMeasurable, true_and]

omit [TopologicalSpace X] [TopologicalSpace Y] [Zero X] [Zero Y] [BorelSpace X] [BorelSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] in
/-- **The weighted rectangle split.** With the Jacobian weight `ρ : X → ℝ` (`ρ ≥ 0`) on the
`X`-factor only, the joint threshold integrand `|G·H|^{−c}·ρ(x)` factorises over a rectangle into
the weighted `X`-integral `∫_U |G|^{−c}·ρ` and the unweighted `Y`-integral `∫_V |H|^{−c}`. -/
private theorem wpm_rect_split (G : X → ℝ) (H : Y → ℝ) (ρ : X → ℝ) (hGm : Measurable G)
    (hHm : Measurable H) (hρm : Measurable ρ) (hρnn : ∀ x, 0 ≤ ρ x) (c : ℝ)
    (U : Set X) (V : Set Y) :
    ∫⁻ p in U ×ˢ V, ENNReal.ofReal (|G p.1 * H p.2| ^ (-c) * ρ p.1)
      = (∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-c) * ρ x))
        * (∫⁻ y in V, ENNReal.ofReal (|H y| ^ (-c))) := by
  have hsplit : (fun p : X × Y => ENNReal.ofReal (|G p.1 * H p.2| ^ (-c) * ρ p.1))
      = (fun p => ENNReal.ofReal (|G p.1| ^ (-c) * ρ p.1) * ENNReal.ofReal (|H p.2| ^ (-c))) := by
    funext p
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hρnn _))]
    congr 1
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    ring
  rw [hsplit, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod_mul
    ((by fun_prop : Measurable (fun x : X => ENNReal.ofReal (|G x| ^ (-c) * ρ x))).aemeasurable)
    ((by fun_prop : Measurable (fun y : Y => ENNReal.ofReal (|H y| ^ (-c)))).aemeasurable)

/-! ## 2. The three directions of the weighted product-min -/

-- ≤ left: joint ≤ X-side weighted threshold, given Y-positivity.
omit [SecondCountableTopology X] in
private theorem wpm_le_left (G : X → ℝ) (H : Y → ℝ) (ρ : X → ℝ) (hGm : Measurable G)
    (hHm : Measurable H) (hρm : Measurable ρ) (hρnn : ∀ x, 0 ≤ ρ x)
    (hHpos : ∀ (c' : ℝ) (V : Set Y), IsOpen V → (0:Y) ∈ V →
      0 < ∫⁻ y in V, ENNReal.ofReal (|H y| ^ (-c'))) :
    weightedThreshold (fun p : X × Y => G p.1 * H p.2) (fun p => ρ p.1) {(0, 0)}
      ≤ weightedThreshold G ρ {0} := by
  unfold weightedThreshold
  apply sSup_le_sSup
  rintro c ⟨c', rfl, Ω, hΩopen, hmem, hint⟩
  obtain ⟨U, V, hUopen, hVopen, h0U, h0V, hsub⟩ := isOpen_prod_iff.1 hΩopen 0 0 (hmem rfl)
  refine ⟨c', rfl, U, hUopen, Set.singleton_subset_iff.2 h0U, ?_⟩
  have hjoint_int : IntegrableOn
      (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ)) * (fun p => ρ p.1) p) (U ×ˢ V) volume :=
    hint.mono_set (by intro p hp; exact hsub ⟨hp.1, hp.2⟩)
  have hjoint_lt : ∫⁻ p in U ×ˢ V, ENNReal.ofReal (|G p.1 * H p.2| ^ (-(c':ℝ)) * ρ p.1) < ⊤ := by
    have hjm : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ)) * ρ p.1) := by
      have : Measurable (fun p : X × Y => G p.1 * H p.2) :=
        (hGm.comp measurable_fst).mul (hHm.comp measurable_snd)
      have : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ))) := by fun_prop
      exact this.mul (hρm.comp measurable_fst)
    rw [← wpm_intOn_iff_lt _ hjm
      (fun p => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hρnn _)) (U ×ˢ V)]
    exact hjoint_int
  rw [wpm_rect_split G H ρ hGm hHm hρm hρnn c' U V] at hjoint_lt
  have hVpos := hHpos (c':ℝ) V hVopen h0V
  have hUlt : ∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-(c':ℝ)) * ρ x) < ⊤ := by
    rw [ENNReal.mul_lt_top_iff] at hjoint_lt
    rcases hjoint_lt with ⟨h1, _⟩ | h1 | h2
    · exact h1
    · rw [h1]; exact ENNReal.zero_lt_top
    · exact absurd h2 hVpos.ne'
  exact (wpm_intOn_iff_lt _ (by fun_prop)
    (fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hρnn _)) U).mpr hUlt

-- ≤ right: joint ≤ rlctAtOn H 0, given X-side weighted positivity.
omit [SecondCountableTopology X] in
private theorem wpm_le_right (G : X → ℝ) (H : Y → ℝ) (ρ : X → ℝ) (hGm : Measurable G)
    (hHm : Measurable H) (hρm : Measurable ρ) (hρnn : ∀ x, 0 ≤ ρ x)
    (hGpos : ∀ (c' : ℝ) (U : Set X), IsOpen U → (0:X) ∈ U →
      0 < ∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-c') * ρ x)) :
    weightedThreshold (fun p : X × Y => G p.1 * H p.2) (fun p => ρ p.1) {(0, 0)}
      ≤ rlctAtOn H 0 := by
  unfold rlctAtOn weightedThreshold
  apply sSup_le_sSup
  rintro c ⟨c', rfl, Ω, hΩopen, hmem, hint⟩
  obtain ⟨U, V, hUopen, hVopen, h0U, h0V, hsub⟩ := isOpen_prod_iff.1 hΩopen 0 0 (hmem rfl)
  refine ⟨c', rfl, V, hVopen, Set.singleton_subset_iff.2 h0V, ?_⟩
  have hjoint_int : IntegrableOn
      (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ)) * (fun p => ρ p.1) p) (U ×ˢ V) volume :=
    hint.mono_set (by intro p hp; exact hsub ⟨hp.1, hp.2⟩)
  have hjoint_lt : ∫⁻ p in U ×ˢ V, ENNReal.ofReal (|G p.1 * H p.2| ^ (-(c':ℝ)) * ρ p.1) < ⊤ := by
    have hjm : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ)) * ρ p.1) := by
      have : Measurable (fun p : X × Y => G p.1 * H p.2) :=
        (hGm.comp measurable_fst).mul (hHm.comp measurable_snd)
      have : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ))) := by fun_prop
      exact this.mul (hρm.comp measurable_fst)
    rw [← wpm_intOn_iff_lt _ hjm
      (fun p => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hρnn _)) (U ×ˢ V)]
    exact hjoint_int
  rw [wpm_rect_split G H ρ hGm hHm hρm hρnn c' U V] at hjoint_lt
  have hUpos := hGpos (c':ℝ) U hUopen h0U
  have hVlt : ∫⁻ y in V, ENNReal.ofReal (|H y| ^ (-(c':ℝ))) < ⊤ := by
    rw [ENNReal.mul_lt_top_iff] at hjoint_lt
    rcases hjoint_lt with ⟨_, h2⟩ | h1 | h2
    · exact h2
    · exact absurd h1 hUpos.ne'
    · rw [h2]; exact ENNReal.zero_lt_top
  have hHint : IntegrableOn (fun y => |H y|^(-(c':ℝ))) V volume :=
    (wpm_intOn_iff_lt _ (by fun_prop) (fun y => Real.rpow_nonneg (abs_nonneg _) _) V).mpr hVlt
  exact hHint.congr_fun (fun y _ => by rw [mul_one]) hVopen.measurableSet

-- ≥: min ≤ joint, via per-factor down-set extractors.
omit [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y] in
private theorem wpm_ge (G : X → ℝ) (H : Y → ℝ) (ρ : X → ℝ) (hGm : Measurable G)
    (hHm : Measurable H) (hρm : Measurable ρ) (hρnn : ∀ x, 0 ≤ ρ x)
    (hdown : ∀ (q : NNReal), (q:ℝ≥0∞) < weightedThreshold G ρ {0} →
      ∃ U : Set X, IsOpen U ∧ (0:X) ∈ U ∧
        IntegrableOn (fun x => |G x| ^ (-(q : ℝ)) * ρ x) U volume)
    (hdownH : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn H 0 →
      ∃ V : Set Y, IsOpen V ∧ (0:Y) ∈ V ∧ IntegrableOn (fun y => |H y| ^ (-(q : ℝ))) V volume) :
    min (weightedThreshold G ρ {0}) (rlctAtOn H 0)
      ≤ weightedThreshold (fun p : X × Y => G p.1 * H p.2) (fun p => ρ p.1) {(0,0)} := by
  apply le_of_forall_lt_imp_le_of_dense
  intro q hq
  rw [lt_min_iff] at hq
  obtain ⟨hqG, hqH⟩ := hq
  have hqfin : q ≠ ⊤ := hqG.ne_top
  set q' := q.toNNReal with hq'
  have hq'e : (q' : ℝ≥0∞) = q := ENNReal.coe_toNNReal hqfin
  obtain ⟨U, hUopen, h0U, hUint⟩ := hdown q' (hq'e ▸ hqG)
  obtain ⟨V, hVopen, h0V, hVint⟩ := hdownH q' (hq'e ▸ hqH)
  apply le_sSup
  refine ⟨q', hq'e.symm, U ×ˢ V, hUopen.prod hVopen, Set.singleton_subset_iff.2 ⟨h0U, h0V⟩, ?_⟩
  have hUlt := (wpm_intOn_iff_lt _ (by fun_prop)
    (fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hρnn _)) U).mp hUint
  have hVlt := (wpm_intOn_iff_lt _ (by fun_prop)
    (fun y => Real.rpow_nonneg (abs_nonneg _) _) V).mp hVint
  have hjm : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(q':ℝ)) * ρ p.1) := by
    have : Measurable (fun p : X × Y => G p.1 * H p.2) :=
      (hGm.comp measurable_fst).mul (hHm.comp measurable_snd)
    have : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(q':ℝ))) := by fun_prop
    exact this.mul (hρm.comp measurable_fst)
  refine (wpm_intOn_iff_lt (fun p => |G p.1 * H p.2|^(-(q':ℝ)) * (fun p => ρ p.1) p)
    hjm (fun p => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hρnn _)) (U ×ˢ V)).mpr ?_
  rw [wpm_rect_split G H ρ hGm hHm hρm hρnn (q':ℝ) U V]
  exact ENNReal.mul_lt_top hUlt hVlt

/-- **The OUTER weighted product-min (generic `X`-side).** For a loss `G(x)·H(y)` over disjoint
groups with the Jacobian weight `ρ(x)` on the `X`-factor, the joint weighted threshold is the min of
the `X`-side weighted threshold and the `Y`-side `rlctAtOn`. Takes the four discharged-at-use-site
hypotheses (positivity on both sides for the `≤` corners, down-set extractors for `≥`), exactly as
`product_min_rlct`. -/
theorem weightedProductMin_rlct (G : X → ℝ) (H : Y → ℝ) (ρ : X → ℝ) (hGm : Measurable G)
    (hHm : Measurable H) (hρm : Measurable ρ) (hρnn : ∀ x, 0 ≤ ρ x)
    (hGpos : ∀ (c' : ℝ) (U : Set X), IsOpen U → (0:X) ∈ U →
      0 < ∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-c') * ρ x))
    (hHpos : ∀ (c' : ℝ) (V : Set Y), IsOpen V → (0:Y) ∈ V →
      0 < ∫⁻ y in V, ENNReal.ofReal (|H y| ^ (-c')))
    (hdown : ∀ (q : NNReal), (q:ℝ≥0∞) < weightedThreshold G ρ {0} →
      ∃ U : Set X, IsOpen U ∧ (0:X) ∈ U ∧
        IntegrableOn (fun x => |G x| ^ (-(q : ℝ)) * ρ x) U volume)
    (hdownH : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn H 0 →
      ∃ V : Set Y, IsOpen V ∧ (0:Y) ∈ V ∧ IntegrableOn (fun y => |H y| ^ (-(q : ℝ))) V volume) :
    weightedThreshold (fun p : X × Y => G p.1 * H p.2) (fun p => ρ p.1) {(0,0)}
      = min (weightedThreshold G ρ {0}) (rlctAtOn H 0) := by
  apply le_antisymm
  · apply le_min (wpm_le_left G H ρ hGm hHm hρm hρnn hHpos)
    exact wpm_le_right G H ρ hGm hHm hρm hρnn hGpos
  · exact wpm_ge G H ρ hGm hHm hρm hρnn hdown hdownH

/-! ## 3. The concrete `y₀`-side: `weightedThreshold (y²) (|y|^e) {0} = (e+1)/2`

The `D₀` exceptional-divisor factor of the blow-up: the loss `y₀²` with the Jacobian weight
`|y₀|^e` (`e = mk − 1 : ℕ`). The integrand `|y₀²|^{−c'}·|y₀|^e` equals `|y₀|^{e − 2c'}` off the
origin, so it is integrable on a symmetric chart iff `e − 2c' > −1 ⇔ c' < (e+1)/2`. -/

/-- The integrand `|y²|^{−s}·|y|^e` agrees with `|y|^{e − 2s}` on the positive ray
(where `|y| = y`).
The pointwise identity behind the `y₀`-side admissibility iff. -/
private theorem mono1D_integrand_eq (e : ℕ) (s : ℝ) {y : ℝ} (hy : 0 < y) :
    |y ^ 2| ^ (-s) * |y| ^ e = |y| ^ ((e : ℝ) - 2 * s) := by
  have hyabs : |y| = y := abs_of_pos hy
  rw [hyabs, abs_of_pos (by positivity : (0:ℝ) < y ^ 2)]
  rw [← Real.rpow_natCast y e, ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le,
    ← Real.rpow_add hy]
  ring_nf

/-- **`y₀`-side admissibility iff.** For `c' : NNReal`, some open `Ω ∋ 0` carries the weighted
integrand `|y²|^{−c'}·|y|^e` integrably **iff** `c' < (e+1)/2`. The weighted analog of
`smoothBlock1D_admissible_iff` (`e = 0` recovers it up to the `·1` weight). -/
theorem weightedMono1D_admissible_iff (e : ℕ) (c' : NNReal) :
    (∃ Ω : Set ℝ, IsOpen Ω ∧ (0 : ℝ) ∈ Ω ∧
        IntegrableOn (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e) Ω volume)
      ↔ (c' : ℝ) < ((e : ℝ) + 1) / 2 := by
  constructor
  · rintro ⟨Ω, hΩopen, h0, hint⟩
    obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hΩopen.mem_nhds h0)
    set ε := min (-l) u with hε
    have hεpos : 0 < ε := lt_min (by linarith [hlu.1]) hlu.2
    have hIoosub : Ioo (-ε) ε ⊆ Ω := fun y hy =>
      hsub ⟨by linarith [hy.1, min_le_left (-l) u], by linarith [hy.2, min_le_right (-l) u]⟩
    have hr := hint.mono_set hIoosub
    have hIccsub : Icc (-(ε / 2)) (ε / 2) ⊆ Ioo (-ε) ε :=
      fun y hy => ⟨by linarith [hy.1, hεpos], by linarith [hy.2, hεpos]⟩
    have hr2 := hr.mono_set hIccsub
    -- on the positive sub-ray the integrand equals `y^{e − 2c'}` (`|y| = y`); apply the rpow iff.
    have hpos_eq : EqOn (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e)
        (fun y : ℝ => y ^ ((e : ℝ) - 2 * (c' : ℝ))) (Ioo (0 : ℝ) (ε / 2)) := fun y hy => by
      show |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e = y ^ ((e : ℝ) - 2 * (c' : ℝ))
      rw [mono1D_integrand_eq e (c' : ℝ) hy.1, abs_of_pos hy.1]
    have hsubIoo : Ioo (0 : ℝ) (ε / 2) ⊆ Icc (-(ε / 2)) (ε / 2) :=
      fun y hy => ⟨by linarith [hy.1, hεpos], hy.2.le⟩
    have hr3 := (hr2.mono_set hsubIoo).congr_fun hpos_eq measurableSet_Ioo
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by linarith : (0:ℝ) < ε / 2)] at hr3
    linarith
  · intro hc
    refine ⟨Ioo (-1) 1, isOpen_Ioo, by norm_num, ?_⟩
    -- integrable on the symmetric interval via the symmetric rpow iff, then transfer.
    have habs : IntegrableOn (fun y : ℝ => |y| ^ ((e : ℝ) - 2 * (c' : ℝ)))
        (Icc (-(1:ℝ)) 1) volume := by
      rw [abs_rpow_integrableOn_Icc_symm _ _ (by norm_num : (0:ℝ) < 1)]
      have : (c' : ℝ) < ((e : ℝ) + 1) / 2 := hc
      linarith
    -- transfer to the weighted integrand on the positive ray; glue the negative ray by symmetry.
    have hposEq : EqOn (fun y : ℝ => |y| ^ ((e : ℝ) - 2 * (c' : ℝ)))
        (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e) (Ioo (0 : ℝ) 1) :=
      fun y hy => (mono1D_integrand_eq e (c' : ℝ) hy.1).symm
    have hwpos : IntegrableOn (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e)
        (Icc (0:ℝ) 1) volume := by
      rw [integrableOn_Icc_iff_integrableOn_Ioo]
      refine (habs.mono_set ?_).congr_fun hposEq measurableSet_Ioo
      exact fun y hy => ⟨by linarith [hy.1], hy.2.le⟩
    have hweven : (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e)
        = (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e) ∘ (fun y : ℝ => -y) := by
      funext y; simp only [Function.comp_apply, neg_sq, abs_neg]
    have hwneg : IntegrableOn (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e)
        (Icc (-(1:ℝ)) 0) volume := by
      have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (measurableEmbedding_neg (α := ℝ))
        (f := fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e) (s := Icc (0 : ℝ) 1)
      have hpre : (fun y : ℝ => -y) ⁻¹' Icc (0 : ℝ) 1 = Icc (-(1:ℝ)) 0 := by
        ext y; simp only [mem_preimage, mem_Icc, neg_nonneg]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [hpre, ← hweven] at hmp
      exact hmp.2 hwpos
    have hunion : Icc (-(1:ℝ)) 1 = Icc (-(1:ℝ)) 0 ∪ Icc (0 : ℝ) 1 :=
      (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
    have hfull : IntegrableOn (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e)
        (Icc (-(1:ℝ)) 1) volume := by
      rw [hunion]; exact hwneg.union hwpos
    exact hfull.mono_set Ioo_subset_Icc_self

/-- **The `y₀`-side weighted threshold value.** `weightedThreshold (y²) (|y|^e) {0} = (e+1)/2`. With
`e = mk − 1` this is `mk/2`, the `D₀` exceptional-divisor ratio of the blow-up. -/
theorem weightedMono1D_threshold (e : ℕ) :
    weightedThreshold (fun y : ℝ => y ^ 2) (fun y : ℝ => |y| ^ e) {(0 : ℝ)}
      = ((e : ℝ≥0∞) + 1) / 2 := by
  unfold weightedThreshold
  have hset : { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧
        ∃ Ω : Set ℝ, IsOpen Ω ∧ {(0 : ℝ)} ⊆ Ω ∧
          IntegrableOn (fun y : ℝ => |y ^ 2| ^ (-(c' : ℝ)) * |y| ^ e) Ω volume }
      = { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧ (c' : ℝ) < ((e : ℝ) + 1) / 2 } := by
    ext c; constructor
    · rintro ⟨c', rfl, Ω, hΩopen, h0, hint⟩
      exact ⟨c', rfl, (weightedMono1D_admissible_iff e c').1 ⟨Ω, hΩopen, h0 rfl, hint⟩⟩
    · rintro ⟨c', rfl, hc⟩
      obtain ⟨Ω, hΩopen, h0, hint⟩ := (weightedMono1D_admissible_iff e c').2 hc
      exact ⟨c', rfl, Ω, hΩopen, by simpa using h0, hint⟩
  rw [hset]
  -- the threshold value `(e+1)/2` as the sSup of the coerced down-set `{c' : c' < (e+1)/2}`.
  have htfin : ((e : ℝ≥0∞) + 1) / 2 ≠ ⊤ :=
    (ENNReal.div_lt_top (by simp) (by norm_num)).ne
  have htreal : (((e : ℝ≥0∞) + 1) / 2).toReal = ((e : ℝ) + 1) / 2 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)]; simp
  apply le_antisymm
  · apply sSup_le; rintro c ⟨c', rfl, hc⟩
    rw [← ENNReal.ofReal_toReal htfin, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [htreal]; exact hc.le
  · apply le_of_forall_lt_imp_le_of_dense
    intro q hq
    have hqfin : q ≠ ⊤ := hq.ne_top
    apply le_sSup
    refine ⟨q.toNNReal, (ENNReal.coe_toNNReal hqfin).symm, ?_⟩
    have hqt : q.toReal < ((e : ℝ) + 1) / 2 := by
      have := (ENNReal.toReal_lt_toReal hqfin htfin).2 hq
      rwa [htreal] at this
    simpa using hqt

/-! ## 4. The assembled two-strata `y₀`-side product-min (cert-104b §4(2))

The OUTER product-min the per-node cover datum consumes, with the concrete `D₀`-divisor `y₀`-side
plugged in and its threshold evaluated to `(e+1)/2 = mk/2`. The `Y`-side (the residual `core`) is
taken via `K ≠ 0 a.e.` exactly as in `product_min_rlct_of_ne`. -/

/-- **`y₀`-side weighted-integral positivity.** For open `U ∋ 0` in `ℝ`, the weighted integrand
`|y²|^{−c'}·|y|^e` has strictly positive integral: it is `> 0` off the null set `{0}`, and `U` has
positive measure. -/
private theorem mono1D_weighted_pos (e : ℕ) (c' : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (h0 : (0 : ℝ) ∈ U) :
    0 < ∫⁻ y in U, ENNReal.ofReal (|y ^ 2| ^ (-c') * |y| ^ e) := by
  set f : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (|y ^ 2| ^ (-c') * |y| ^ e) with hf
  have hfmeas : Measurable f := by fun_prop
  rw [setLIntegral_pos_iff hfmeas]
  have hsub : {y : ℝ | y ≠ 0} ⊆ Function.support f := by
    intro y hy
    have hypos : 0 < |y| := abs_pos.2 hy
    have hy2 : 0 < |y ^ 2| := abs_pos.2 (pow_ne_zero 2 hy)
    have h1 : 0 < |y ^ 2| ^ (-c') := Real.rpow_pos_of_pos hy2 _
    have h2 : 0 < |y| ^ e := pow_pos hypos e
    simp only [Function.mem_support, hf, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos h1 h2
  have hnull : (volume : Measure ℝ) {y : ℝ | y = 0} = 0 := by
    rw [show {y : ℝ | y = 0} = {(0 : ℝ)} by ext y; simp]
    exact measure_singleton 0
  have hUle : (volume : Measure ℝ) U ≤ volume ({y : ℝ | y ≠ 0} ∩ U) := by
    have hsplit : U ⊆ ({y : ℝ | y ≠ 0} ∩ U) ∪ ({y : ℝ | y = 0} ∩ U) := by
      intro y hy; by_cases hg : y = 0
      · exact Or.inr ⟨hg, hy⟩
      · exact Or.inl ⟨hg, hy⟩
    calc (volume : Measure ℝ) U
        ≤ volume (({y : ℝ | y ≠ 0} ∩ U) ∪ ({y : ℝ | y = 0} ∩ U)) := measure_mono hsplit
      _ ≤ volume ({y : ℝ | y ≠ 0} ∩ U) + volume ({y : ℝ | y = 0} ∩ U) := measure_union_le _ _
      _ = volume ({y : ℝ | y ≠ 0} ∩ U) := by
          rw [measure_inter_null_of_null_left U hnull, add_zero]
  calc (0 : ℝ≥0∞) < volume U := hU.measure_pos _ ⟨0, h0⟩
    _ ≤ volume ({y : ℝ | y ≠ 0} ∩ U) := hUle
    _ ≤ volume (Function.support f ∩ U) := measure_mono (Set.inter_subset_inter_left U hsub)

/-- **The OUTER weighted product-min, FINAL form (cert-104b §4(2)).** For the `D₀`-divisor `y₀`-side
`y₀²` carrying the Jacobian weight `|y₀|^e` (`e = mk − 1`), disjoint from a core `K(z)` that is
`≠ 0 a.e.`, the joint weighted threshold of `y₀²·K(z)` is

  `weightedThreshold (fun p => p.1² · K p.2) (fun p => |p.1|^e) {(0,0)} = min ((e+1)/2) (rlctAtOn K 0)`.

With `e = mk − 1` the `y₀`-side value `(e+1)/2 = mk/2`. The single statement the per-node cover datum
consumes (the bridge from `rlct(core)` to the true-loss `rlct(F)` — the new Core RLCT content of the
binding-R1 general per-node `hstep`). -/
theorem weightedProductMin_mono1D_of_ne
    {Z : Type*} [PseudoMetricSpace Z] [MeasureSpace Z] [ProperSpace Z]
    [IsFiniteMeasureOnCompacts (volume : Measure Z)]
    [MeasureTheory.Measure.IsOpenPosMeasure (volume : Measure Z)]
    [SFinite (volume : Measure Z)] [Zero Z] [BorelSpace Z] [SecondCountableTopology Z]
    (e : ℕ) (K : Z → ℝ) (hKm : Measurable K)
    (hKne : ∀ᵐ z ∂(volume : Measure Z), K z ≠ 0) :
    weightedThreshold (fun p : ℝ × Z => p.1 ^ 2 * K p.2) (fun p => |p.1| ^ e) {(0, 0)}
      = min (((e : ℝ≥0∞) + 1) / 2) (rlctAtOn K 0) := by
  have hmin := weightedProductMin_rlct (X := ℝ) (Y := Z)
    (fun y : ℝ => y ^ 2) K (fun y : ℝ => |y| ^ e)
    (by fun_prop) hKm (by fun_prop) (fun y => by positivity)
    -- hGpos: X-side weighted positivity
    (fun c' U hU h0 => mono1D_weighted_pos e c' U hU h0)
    -- hHpos: Y-side positivity from K ≠ 0 a.e.
    (fun c' V hV h0 => by
      set g : Z → ℝ≥0∞ := fun z => ENNReal.ofReal (|K z| ^ (-c')) with hg
      have hgmeas : Measurable g := by fun_prop
      rw [setLIntegral_pos_iff hgmeas]
      have hsub : {z : Z | K z ≠ 0} ⊆ Function.support g := by
        intro z hz
        have : 0 < |K z| ^ (-c') := Real.rpow_pos_of_pos (abs_pos.2 hz) _
        simp only [Function.mem_support, hg, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact this
      have hnull : (volume : Measure Z) {z : Z | K z = 0} = 0 := by
        rw [show {z : Z | K z = 0} = {z : Z | K z ≠ 0}ᶜ by ext z; simp]
        exact (MeasureTheory.ae_iff.1 hKne)
      have hVle : (volume : Measure Z) V ≤ volume ({z : Z | K z ≠ 0} ∩ V) := by
        have hsplit : V ⊆ ({z : Z | K z ≠ 0} ∩ V) ∪ ({z : Z | K z = 0} ∩ V) := by
          intro z hz; by_cases hzk : K z = 0
          · exact Or.inr ⟨hzk, hz⟩
          · exact Or.inl ⟨hzk, hz⟩
        calc (volume : Measure Z) V
            ≤ volume (({z : Z | K z ≠ 0} ∩ V) ∪ ({z : Z | K z = 0} ∩ V)) := measure_mono hsplit
          _ ≤ volume ({z : Z | K z ≠ 0} ∩ V) + volume ({z : Z | K z = 0} ∩ V) := measure_union_le _ _
          _ = volume ({z : Z | K z ≠ 0} ∩ V) := by
              rw [measure_inter_null_of_null_left V hnull, add_zero]
      calc (0 : ℝ≥0∞) < volume V := hV.measure_pos _ ⟨0, h0⟩
        _ ≤ volume ({z : Z | K z ≠ 0} ∩ V) := hVle
        _ ≤ volume (Function.support g ∩ V) := measure_mono (Set.inter_subset_inter_left V hsub))
    -- hdown: X-side down-set from the explicit admissibility iff
    (fun q hq => by
      rw [weightedMono1D_threshold e] at hq
      have hqlt : (q : ℝ) < ((e : ℝ) + 1) / 2 := by
        have htfin : ((e : ℝ≥0∞) + 1) / 2 ≠ ⊤ := (ENNReal.div_lt_top (by simp) (by norm_num)).ne
        have := (ENNReal.toReal_lt_toReal (by simp) htfin).2 hq
        rwa [ENNReal.coe_toReal,
          show (((e : ℝ≥0∞) + 1) / 2).toReal = ((e : ℝ) + 1) / 2 by
            rw [ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)]; simp] at this
      exact (weightedMono1D_admissible_iff e q).2 hqlt)
    -- hdownH: Y-side down-set
    (fun q hq => core_admissible_of_lt K hKm 0 q hq)
  -- rewrite the X-side weighted threshold to its value (e+1)/2.
  rw [weightedMono1D_threshold e] at hmin
  exact hmin

end DLNFibre.DLN.RLCT
