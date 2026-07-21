import DLNFibre.Core.Analysis.RLCT.Local
import DLNFibre.Core.Analysis.RLCT.LocalMono
import DLNFibre.Core.Analysis.RLCT.Basic
import Meta.Cordon

/-!
# `Core.Aoyagi.IdealInvariance` — Object A: RLCT ideal-invariance (Aoyagi Lemma 1), two-sided

**LANDED (v3, sorry-free).** This module is fully struck: every headline is proven, no `@[blueprint]`
forecast and no `sorry` remains. The forecast leaves — the Cauchy–Schwarz domination, the
junk-guarded germ-monotonicity, positive scaling, and their two-sided ideal-invariance wiring
(weighted and unweighted) — are all discharged below.

## The object (Aoyagi Lemma 1, corrected sign; worked.tex:153–165)

For analytic families `F : Fin m → (ℝⁿ → ℝ)` and `G : Fin p → (ℝⁿ → ℝ)`, if every `Gᵢ` lies in the
germ ideal `⟨F₁,…,F_m⟩` at `x` then
`rlctAt (∑ Gᵢ²) x ≤ rlctAt (∑ Fⱼ²) x`,
and if the two germ ideals are equal the RLCTs are equal. (The worked reproduction prints `≥` at
line 156; that is the paper's sign typo — the correct and Lean-checked direction is `≤`: a family
generating a *larger* vanishing set is *more* singular, so its threshold is *smaller*.)

`⟨F⟩ ⊇ ⟨G⟩` is encoded, at germ generality, by an **explicit continuous representation**
`Gᵢ = ∑ⱼ aᵢⱼ · Fⱼ` near `x` (`GermRepresents`). For polynomial/analytic `F, G` — the DLN case, where
the generators are matrix-product entries — this is *exactly* ideal membership in the local ring
(the coefficients are polynomials, hence continuous). Stating A over the representation keeps it TRUE
at full germ generality with no hidden analytic monument, and makes the pointwise domination
`∑ Gᵢ² ≤ C · ∑ Fⱼ²` a Cauchy–Schwarz + local-boundedness computation.

## The weighted carrier `wrlctAt` (the change-of-variables carrier for Object B)

`wrlctAt W K x` is the RLCT of `K` against a nonnegative analytic **weight** `W` in the measure:
`sSup { c ≥ 0 | w ↦ W w · K w ^(-c) integrable near x }`. This is the object the proper-map
change-of-variables of Object B produces (the Jacobian weight `W = |det Dg|`). Ideal-invariance is
inherited by the weighted form (multiply the pointwise comparison by the nonnegative `W`), which is
why A is stated in both forms and B rides the weighted one.

## The one genuine analytic leaf (named, not hidden)

`rlctAt_mono_of_eventually_le` — germ-monotonicity of `rlctAt` under an eventual domination `K ≤ K'`
near `x`, junk-guarded (`LocallyNullZeros K x`) in place of a strict-positivity hypothesis. The banked
`RLCT.localAdmissibleExponents_subset_of_le` proves exactly this under `0 < K` near `x`; the singular
RLCT setting has `K = ∑ Gᵢ²` vanishing on a positive-dimensional germ, so the strict-positivity form
does not apply and the zero-set (a measure-zero real variety) is handled via the null-zero guard. This
is standard-material proof-engineering (measure-zero adjustment of the banked domination), NOT new
mathematics — it is the module's single strike-able frontier leaf, decomposed to it explicitly.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {n : ℕ}

/-! ## Sum-of-squares germs and germ ideal membership -/

/-- The sum-of-squares germ `∑ᵢ (Fᵢ)²` of a finite family — the polynomial whose RLCT is Aoyagi's
`rlct⟨F⟩` (Def 1, `rlct_{w*}(J) = rlct(∑ Fᵢ²)`; worked.tex:143). -/
noncomputable def sumSqFam {m : ℕ} (F : Fin m → (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun w ↦ ∑ i, (F i w) ^ 2

/-- `∑ᵢ (Fᵢ w)² ≥ 0`. -/
lemma sumSqFam_nonneg {m : ℕ} (F : Fin m → (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) :
    0 ≤ sumSqFam F w :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg _

/-- **Germ ideal membership by an explicit continuous representation.** `GermRepresents G F x`
holds when there are coefficient germs `aᵢⱼ`, continuous at `x`, with `Gᵢ = ∑ⱼ aᵢⱼ · Fⱼ` on a
neighbourhood of `x`. This is the honest germ-level encoding of `Gᵢ ∈ ⟨F₁,…,F_m⟩`: for
polynomial/analytic generators it is exactly local-ring membership (polynomial cofactors). -/
def GermRepresents {m p : ℕ} (G : Fin p → (Fin n → ℝ) → ℝ)
    (F : Fin m → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ a : Fin p → Fin m → (Fin n → ℝ) → ℝ,
    (∀ i j, ContinuousAt (a i j) x) ∧
    (∀ᶠ w in 𝓝 x, ∀ i, G i w = ∑ j, a i j w * F j w)

/-- **Region ideal membership** `Gᵢ ∈ ⟨F⟩` **on a set `V`** by a representation whose coefficients
are continuous ON `V`: `Gᵢ = ∑ⱼ aᵢⱼ · Fⱼ` for all `u ∈ V`. The DOM-WIDE strengthening of
`GermRepresents` (which binds only the germ at a point) — required by Object B's charts so the ideal
identity holds throughout a chart's domain, not merely at its origin (else a chart could cover far
regions where the identity fails). For polynomial/analytic `F, G` the cofactors are polynomial, hence
continuous on any `V`. -/
def RegionRepresents {m p : ℕ} (G : Fin p → (Fin n → ℝ) → ℝ)
    (F : Fin m → (Fin n → ℝ) → ℝ) (V : Set (Fin n → ℝ)) : Prop :=
  ∃ a : Fin p → Fin m → (Fin n → ℝ) → ℝ,
    (∀ i j, ContinuousOn (a i j) V) ∧
    (∀ u ∈ V, ∀ i, G i u = ∑ j, a i j u * F j u)

/-- **The junk-`0` guard.** `LocallyNullZeros K x`: the zero set of `K` is null on some neighbourhood
of `x`. REQUIRED because the banked `negPow` is `Real.rpow` with `0^(-c) = 0` — a *total* ℝ-proxy of
an ℝ∪{∞} invariant whose junk value at a zero INFLATES `rlctAt` when `{K = 0}` has positive measure
(the documented repo hazard, `docs/policies/citation-cordon.md`; counterexample `K = max(w,0)²`
raises `rlctAt` above a strictly-dominating germ). For sum-of-squares of polynomial/analytic families
`{∑ Fᵢ² = 0} = ⋂ᵢ Z(Fᵢ)` is a proper real-analytic subvariety, hence locally null — so this guard is
dischargeable at every point of use, and it is the honest hypothesis the monotonicity needs. -/
def LocallyNullZeros (K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ s ∈ 𝓝 x, volume ({w | K w = 0} ∩ s) = 0

/-! ## Shared scaling / integrability helpers -/

/-- For a positive scalar `C`, `Real.rpow` factors through the left multiplication:
`(C * t) ^ y = C ^ y * t ^ y` for ALL real `t` — including `t ≤ 0`, where the shared `cos (y·π)`
phase cancels. (Mathlib's `Real.mul_rpow` needs both factors nonnegative.) -/
private lemma rpow_pos_mul_left {C : ℝ} (hC : 0 < C) (t y : ℝ) :
    (C * t) ^ y = C ^ y * t ^ y := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rcases eq_or_ne y 0 with hy | hy
    · subst hy; simp
    · rw [mul_zero, Real.zero_rpow hy, mul_zero]
  · rcases lt_or_gt_of_ne ht with htneg | htpos
    · have hCt : C * t < 0 := mul_neg_of_pos_of_neg hC htneg
      rw [Real.rpow_def_of_neg hCt, Real.rpow_def_of_neg htneg, Real.rpow_def_of_pos hC,
        Real.log_mul hC.ne' ht, add_mul, Real.exp_add]
      ring
    · exact Real.mul_rpow hC.le htpos.le

/-- Multiplying an integrand by a nonzero real constant preserves integrability-at-a-filter. -/
private lemma integrableAtFilter_const_mul_iff {f : (Fin n → ℝ) → ℝ}
    {l : Filter (Fin n → ℝ)} {D : ℝ} (hD : D ≠ 0) :
    IntegrableAtFilter (fun w ↦ D * f w) l ↔ IntegrableAtFilter f l := by
  have key : ∀ (E : ℝ) (g : (Fin n → ℝ) → ℝ),
      IntegrableAtFilter g l → IntegrableAtFilter (fun w ↦ E * g w) l := by
    intro E g hg
    have h2 := hg.smul E
    have heq : (E • g) = (fun w ↦ E * g w) := by funext w; simp only [Pi.smul_apply, smul_eq_mul]
    rwa [heq] at h2
  refine ⟨fun h ↦ ?_, fun h ↦ key D f h⟩
  have h2 := key D⁻¹ _ h
  have heq : (fun w ↦ D⁻¹ * (D * f w)) = f := by
    funext w; rw [← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  rwa [heq] at h2

/-- Positive scaling of the germ `K` leaves the locally-admissible exponents unchanged: the negative
power `(C·K)^(-c)` differs from `K^(-c)` only by the positive constant `C^(-c)`. -/
lemma localAdmissibleExponents_const_mul {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {C : ℝ} (hC : 0 < C) :
    localAdmissibleExponents (fun w ↦ C * K w) x = localAdmissibleExponents K x := by
  ext c
  simp only [mem_localAdmissibleExponents]
  have hpt : negPow (fun w ↦ C * K w) c = fun w ↦ C ^ (-c) * negPow K c w := by
    funext w; simp only [negPow_apply]; exact rpow_pos_mul_left hC (K w) (-c)
  constructor
  · rintro ⟨h0, hint⟩
    rw [hpt] at hint
    exact ⟨h0, (integrableAtFilter_const_mul_iff (f := negPow K c)
      (Real.rpow_pos_of_pos hC (-c)).ne').1 hint⟩
  · rintro ⟨h0, hint⟩
    refine ⟨h0, ?_⟩
    rw [hpt]
    exact (integrableAtFilter_const_mul_iff (f := negPow K c)
      (Real.rpow_pos_of_pos hC (-c)).ne').2 hint

/-- Shared measure-zero a.e. bound: a pointwise bound holding on `V` off a `volume`-null set `Z ∩ V`
upgrades to an a.e. bound for `volume.restrict V`. The null-zero-set adjustment that lets the banked
strict-positivity domination go through with only the `LocallyNullZeros` guard. -/
private lemma ae_le_of_forall_mem_diff_null {V Z : Set (Fin n → ℝ)}
    {f g : (Fin n → ℝ) → ℝ} (hVmeas : MeasurableSet V) (hZnull : volume (Z ∩ V) = 0)
    (hbd : ∀ w ∈ V, w ∉ Z → ‖f w‖ ≤ g w) :
    ∀ᵐ w ∂(volume.restrict V), ‖f w‖ ≤ g w := by
  have h1 : ∀ᵐ w ∂volume, w ∉ (Z ∩ V) := by
    rw [ae_iff]; simp only [not_not, setOf_mem_eq]; exact hZnull
  filter_upwards [ae_restrict_of_ae (s := V) h1, ae_restrict_mem hVmeas] with w hw hwV
  exact hbd w hwV (fun hwZ ↦ hw ⟨hwZ, hwV⟩)

/-! ## The strike-able analytic leaves (decomposed, statement-locked) -/

/-- **STRIKE-ABLE leaf — Cauchy–Schwarz + local boundedness.** From a continuous representation
`Gᵢ = ∑ⱼ aᵢⱼ Fⱼ` near `x`, the sum-of-squares germ of `G` is dominated by a constant multiple of
that of `F` near `x`: `∃ C ≥ 0, ∀ᶠ w in 𝓝 x, ∑ᵢ (Gᵢ w)² ≤ C · ∑ⱼ (Fⱼ w)²`. Pointwise
Cauchy–Schwarz gives `∑ᵢ (∑ⱼ aᵢⱼ Fⱼ)² ≤ (∑ᵢⱼ aᵢⱼ²)(∑ⱼ Fⱼ²)`; the coefficient sum `∑ᵢⱼ aᵢⱼ²` is
continuous at `x`, hence bounded on a neighbourhood. Proof engineering, no new mathematics. -/
theorem eventually_sumSqFam_le_of_germRepresents {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : GermRepresents G F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in 𝓝 x, sumSqFam G w ≤ C * sumSqFam F w := by
  obtain ⟨a, hacont, hrep⟩ := h
  refine ⟨(∑ i, ∑ j, (a i j x) ^ 2) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ i, ∑ j, (a i j x) ^ 2 :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    linarith
  · have hScont : ContinuousAt (fun w ↦ ∑ i, ∑ j, (a i j w) ^ 2) x := by
      apply tendsto_finset_sum
      intro i _
      apply tendsto_finset_sum
      intro j _
      exact (hacont i j).pow 2
    have hbound : ∀ᶠ w in 𝓝 x,
        (∑ i, ∑ j, (a i j w) ^ 2) < (∑ i, ∑ j, (a i j x) ^ 2) + 1 :=
      Filter.Tendsto.eventually_lt_const (lt_add_one _) hScont
    filter_upwards [hrep, hbound] with w hrepw hboundw
    have hSF : 0 ≤ sumSqFam F w := sumSqFam_nonneg F w
    calc sumSqFam G w
        = ∑ i, (∑ j, a i j w * F j w) ^ 2 := by
          simp only [sumSqFam]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [hrepw i]
      _ ≤ ∑ i, (∑ j, (a i j w) ^ 2) * (∑ j, (F j w) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ a i j w) (fun j ↦ F j w)
      _ = (∑ i, ∑ j, (a i j w) ^ 2) * sumSqFam F w := by
          simp only [sumSqFam]; rw [← Finset.sum_mul]
      _ ≤ ((∑ i, ∑ j, (a i j x) ^ 2) + 1) * sumSqFam F w :=
          mul_le_mul_of_nonneg_right hboundw.le hSF

/-- **STRIKE-ABLE leaf — germ-monotonicity of `rlctAt` under an eventual domination, junk-guarded.**
If `0 ≤ K` and `K ≤ K'` on a neighbourhood of `x` (`hbound`, pointwise-eventual), `K'` measurable,
and `K`'s zero set is locally null (`hKnull` — the junk-`0` guard, WITHOUT which the claim is FALSE:
`negPow K c` is `0` on `{K=0}`, so a positive-measure zero set of the smaller germ `K` inflates
`rlctAt K` above `rlctAt K'`), then `rlctAt K x ≤ rlctAt K' x`. Off the null zero set `K > 0` and the
banked `RLCT.localAdmissibleExponents_subset_of_le`'s a.e. content applies. Standard measure-zero
proof-engineering; the strict-positivity hypothesis of the banked lemma is replaced by `hKnull`. -/
theorem rlctAt_mono_of_eventually_le {K K' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hK'meas : Measurable K') (hbound : ∀ᶠ w in 𝓝 x, 0 ≤ K w ∧ K w ≤ K' w)
    (hKnull : LocallyNullZeros K x)
    (hbdd : BddAbove (localAdmissibleExponents K' x)) :
    rlctAt K x ≤ rlctAt K' x := by
  rw [rlctAt_def, rlctAt_def]
  refine csSup_le_csSup hbdd
    ⟨(0 : ℝ), zero_mem_localAdmissibleExponents (integrableAtFilter_one_nhds x)⟩ ?_
  rintro c ⟨hc0, s₁, hs₁mem, hs₁int⟩
  refine ⟨hc0, ?_⟩
  obtain ⟨sI, hsIsub, hsIopen, hxsI⟩ := mem_nhds_iff.1 hs₁mem
  obtain ⟨tB, htBbound, htBopen, hxtB⟩ := eventually_nhds_iff.1 hbound
  obtain ⟨sN, hsNmem, hsNnull⟩ := hKnull
  obtain ⟨sN', hsN'sub, hsN'open, hxsN'⟩ := mem_nhds_iff.1 hsNmem
  refine ⟨sI ∩ tB ∩ sN', ((hsIopen.inter htBopen).inter hsN'open).mem_nhds
    ⟨⟨hxsI, hxtB⟩, hxsN'⟩, ?_⟩
  have hVmeas : MeasurableSet (sI ∩ tB ∩ sN') :=
    ((hsIopen.inter htBopen).inter hsN'open).measurableSet
  have hdomint : IntegrableOn (negPow K c) (sI ∩ tB ∩ sN') :=
    hs₁int.mono_set fun y hy ↦ hsIsub hy.1.1
  refine Integrable.mono' hdomint (measurable_negPow hK'meas c).aestronglyMeasurable ?_
  refine ae_le_of_forall_mem_diff_null (Z := {w | K w = 0}) hVmeas ?_ ?_
  · exact measure_mono_null
      (inter_subset_inter (Subset.refl _) (fun y hy ↦ hsN'sub hy.2)) hsNnull
  · intro w hwV hwZ
    have hwtB : w ∈ tB := hwV.1.2
    obtain ⟨hK0le, hKle⟩ := htBbound w hwtB
    have hKne : K w ≠ 0 := hwZ
    have hKpos : 0 < K w := lt_of_le_of_ne hK0le hKne.symm
    have hK'pos : 0 < K' w := lt_of_lt_of_le hKpos hKle
    rw [Real.norm_eq_abs, negPow_apply, negPow_apply,
      abs_of_nonneg (Real.rpow_nonneg hK'pos.le _)]
    exact Real.rpow_le_rpow_of_nonpos hKpos hKle (by linarith)

/-- **STRIKE-ABLE leaf — positive scaling leaves `rlctAt` unchanged.** For `C > 0`,
`rlctAt (fun w ↦ C * K w) x = rlctAt K x`: `(C·K)^(-c) = C^(-c) · K^(-c)`, a positive constant
factor never affects local integrability. Proof engineering. -/
theorem rlctAt_const_mul {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {C : ℝ} (hC : 0 < C) :
    rlctAt (fun w ↦ C * K w) x = rlctAt K x := by
  unfold rlctAt
  rw [localAdmissibleExponents_const_mul hC]

/-! ## Object A — the two-sided ideal invariance (WIRED from the leaves) -/

/-- **Object A (≤), Aoyagi Lemma 1, corrected sign.** If every `Gᵢ` lies in `⟨F⟩` at `x`
(`GermRepresents G F x`) and `∑ Gᵢ²`'s zero set is locally null (`hGnull`, the junk-`0` guard), then
`rlctAt (∑ Gᵢ²) x ≤ rlctAt (∑ Fⱼ²) x`. Wired: the representation gives `∑ Gᵢ² ≤ C · ∑ Fⱼ²` near `x`
(domination leaf); junk-guarded monotonicity gives `rlctAt (∑ Gᵢ²) x ≤ rlctAt (C · ∑ Fⱼ²) x`;
positive scaling collapses the constant. `hGnull` is dischargeable for polynomial/analytic `G`. -/
theorem rlctAt_sumSqFam_le_of_germRepresents {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hFmeas : ∀ j, Measurable (F j)) (h : GermRepresents G F x)
    (hGnull : LocallyNullZeros (sumSqFam G) x)
    (hbdd : BddAbove (localAdmissibleExponents (sumSqFam F) x)) :
    rlctAt (sumSqFam G) x ≤ rlctAt (sumSqFam F) x := by
  obtain ⟨C, hC0, hCbound⟩ := eventually_sumSqFam_le_of_germRepresents h
  have hC'pos : (0 : ℝ) < C + 1 := by linarith
  have hsumFmeas : Measurable (sumSqFam F) :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hFmeas i).pow_const 2
  have hbound' : ∀ᶠ w in 𝓝 x,
      0 ≤ sumSqFam G w ∧ sumSqFam G w ≤ (C + 1) * sumSqFam F w := by
    filter_upwards [hCbound] with w hw
    exact ⟨sumSqFam_nonneg G w,
      hw.trans (mul_le_mul_of_nonneg_right (by linarith) (sumSqFam_nonneg F w))⟩
  have hbdd' : BddAbove (localAdmissibleExponents (fun w ↦ (C + 1) * sumSqFam F w) x) := by
    rw [localAdmissibleExponents_const_mul hC'pos]; exact hbdd
  have hmono := rlctAt_mono_of_eventually_le (hsumFmeas.const_mul (C + 1)) hbound' hGnull hbdd'
  rwa [rlctAt_const_mul hC'pos] at hmono

/-- **Object A (=), two-sided ideal invariance.** If the germ ideals coincide (each family lies in
the other's ideal at `x`) and both sum-of-squares zero sets are locally null (`hGnull`, `hFnull` —
the junk-`0` guard applied symmetrically), the sum-of-squares RLCTs are equal. Direct two-sided:
`le_antisymm` of the two junk-guarded containments — the two-way representation makes both `≤`
directions hold, and the null-zero guards defeat the `negPow`-junk symmetrically. Foundational: it
legalises every ideal-preserving step of Object B. Both null guards are dischargeable for
polynomial/analytic families (proper zero sets). -/
theorem rlctAt_sumSqFam_eq_of_germ_eq {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hGmeas : ∀ i, Measurable (G i)) (hFmeas : ∀ j, Measurable (F j))
    (hGnull : LocallyNullZeros (sumSqFam G) x) (hFnull : LocallyNullZeros (sumSqFam F) x)
    (hGbdd : BddAbove (localAdmissibleExponents (sumSqFam G) x))
    (hFbdd : BddAbove (localAdmissibleExponents (sumSqFam F) x))
    (hGF : GermRepresents G F x) (hFG : GermRepresents F G x) :
    rlctAt (sumSqFam G) x = rlctAt (sumSqFam F) x :=
  -- map: A-two-sided (le_antisymm of both junk-guarded containments)
  le_antisymm (rlctAt_sumSqFam_le_of_germRepresents hFmeas hGF hGnull hFbdd)
    (rlctAt_sumSqFam_le_of_germRepresents hGmeas hFG hFnull hGbdd)

/-! ## The weighted RLCT `wrlctAt` and its ideal invariance (the CoV carrier for Object B) -/

/-- Exponents admissible for `K` **against a weight `W`** at `x`: `c ≥ 0` with
`w ↦ W w · K w ^(-c)` integrable near `x`. The weighted analogue of `localAdmissibleExponents`. -/
def wLocalAdmissibleExponents (W K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ IntegrableAtFilter (fun w ↦ W w * negPow K c w) (𝓝 x)}

/-- The **weighted local RLCT** `wrlctAt W K x`: `sSup` of the exponents admissible for `K` against
the nonnegative weight `W`. The object the proper-map change-of-variables of Object B produces (the
Jacobian weight `W = |det Dg|` enters the pulled-back integral). -/
noncomputable def wrlctAt (W K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (wLocalAdmissibleExponents W K x)

/-- The unweighted RLCT is the weight-`1` case (`W ≡ 1`): `wrlctAt 1 K x = rlctAt K x`. -/
theorem wrlctAt_one {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} :
    wrlctAt (fun _ ↦ (1 : ℝ)) K x = rlctAt K x := by
  have hset : wLocalAdmissibleExponents (fun _ ↦ (1 : ℝ)) K x = localAdmissibleExponents K x := by
    ext c
    simp only [wLocalAdmissibleExponents, mem_localAdmissibleExponents, Set.mem_setOf_eq, one_mul]
  unfold wrlctAt
  rw [rlctAt_def, hset]

/-- Positive scaling of the germ leaves the weighted locally-admissible exponents unchanged: the
weighted integrand `W · (C·K)^(-c)` differs from `W · K^(-c)` only by the positive constant
`C^(-c)`. -/
lemma wLocalAdmissibleExponents_const_mul {W K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {C : ℝ} (hC : 0 < C) :
    wLocalAdmissibleExponents W (fun w ↦ C * K w) x = wLocalAdmissibleExponents W K x := by
  ext c
  simp only [wLocalAdmissibleExponents, Set.mem_setOf_eq]
  have hpt : (fun w ↦ W w * negPow (fun w ↦ C * K w) c w)
           = (fun w ↦ C ^ (-c) * (W w * negPow K c w)) := by
    funext w
    simp only [negPow_apply]
    rw [rpow_pos_mul_left hC (K w) (-c)]; ring
  constructor
  · rintro ⟨h0, hint⟩
    rw [hpt] at hint
    exact ⟨h0, (integrableAtFilter_const_mul_iff (f := fun w ↦ W w * negPow K c w)
      (Real.rpow_pos_of_pos hC (-c)).ne').1 hint⟩
  · rintro ⟨h0, hint⟩
    refine ⟨h0, ?_⟩
    rw [hpt]
    exact (integrableAtFilter_const_mul_iff (f := fun w ↦ W w * negPow K c w)
      (Real.rpow_pos_of_pos hC (-c)).ne').2 hint

/-- Positive scaling of the germ leaves the weighted RLCT unchanged. -/
theorem wrlctAt_const_mul {W K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {C : ℝ} (hC : 0 < C) :
    wrlctAt W (fun w ↦ C * K w) x = wrlctAt W K x := by
  unfold wrlctAt
  rw [wLocalAdmissibleExponents_const_mul hC]

/-- **The weighted admissible set is monotone under eventual domination, junk-guarded.** If `0 ≤ W`
and `0 ≤ K ≤ K'` near `x` (with `K`'s zero set locally null), then every exponent admissible for `K`
against `W` is admissible for `K'`. This is the set-level core of `wrlctAt_mono_of_eventually_le`,
exposed so the two-sided version can conclude *set equality* (hence a `wrlctAt` equality with NO
`BddAbove` hypothesis). -/
theorem wLocalAdmissibleExponents_subset_of_eventually_le {W K K' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hWmeas : Measurable W) (hK'meas : Measurable K')
    (hW : ∀ᶠ w in 𝓝 x, 0 ≤ W w)
    (hbound : ∀ᶠ w in 𝓝 x, 0 ≤ K w ∧ K w ≤ K' w)
    (hKnull : LocallyNullZeros K x) :
    wLocalAdmissibleExponents W K x ⊆ wLocalAdmissibleExponents W K' x := by
  rintro c ⟨hc0, s₁, hs₁mem, hs₁int⟩
  refine ⟨hc0, ?_⟩
  obtain ⟨sI, hsIsub, hsIopen, hxsI⟩ := mem_nhds_iff.1 hs₁mem
  obtain ⟨tB, htBbound, htBopen, hxtB⟩ := eventually_nhds_iff.1 hbound
  obtain ⟨tW, htWnn, htWopen, hxtW⟩ := eventually_nhds_iff.1 hW
  obtain ⟨sN, hsNmem, hsNnull⟩ := hKnull
  obtain ⟨sN', hsN'sub, hsN'open, hxsN'⟩ := mem_nhds_iff.1 hsNmem
  refine ⟨sI ∩ tB ∩ tW ∩ sN',
    (((hsIopen.inter htBopen).inter htWopen).inter hsN'open).mem_nhds
      ⟨⟨⟨hxsI, hxtB⟩, hxtW⟩, hxsN'⟩, ?_⟩
  have hVmeas : MeasurableSet (sI ∩ tB ∩ tW ∩ sN') :=
    (((hsIopen.inter htBopen).inter htWopen).inter hsN'open).measurableSet
  have hdomint : IntegrableOn (fun w ↦ W w * negPow K c w) (sI ∩ tB ∩ tW ∩ sN') :=
    hs₁int.mono_set fun y hy ↦ hsIsub hy.1.1.1
  refine Integrable.mono' hdomint
    ((hWmeas.mul (measurable_negPow hK'meas c)).aestronglyMeasurable) ?_
  refine ae_le_of_forall_mem_diff_null (Z := {w | K w = 0}) hVmeas ?_ ?_
  · exact measure_mono_null
      (inter_subset_inter (Subset.refl _) (fun y hy ↦ hsN'sub hy.2)) hsNnull
  · intro w hwV hwZ
    have hwtB : w ∈ tB := hwV.1.1.2
    have hwtW : w ∈ tW := hwV.1.2
    obtain ⟨hK0le, hKle⟩ := htBbound w hwtB
    have hWnn : 0 ≤ W w := htWnn w hwtW
    have hKne : K w ≠ 0 := hwZ
    have hKpos : 0 < K w := lt_of_le_of_ne hK0le hKne.symm
    have hK'pos : 0 < K' w := lt_of_lt_of_le hKpos hKle
    have hpow : negPow K' c w ≤ negPow K c w := by
      simp only [negPow_apply]
      exact Real.rpow_le_rpow_of_nonpos hKpos hKle (by linarith)
    have hpow'nn : 0 ≤ negPow K' c w := negPow_nonneg hK'pos.le c
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hWnn hpow'nn)]
    exact mul_le_mul_of_nonneg_left hpow hWnn

/-- Weighted germ-monotonicity of `wrlctAt` under an eventual domination, junk-guarded — the
weighted analogue of `rlctAt_mono_of_eventually_le`. The nonnegative weight `W` preserves the a.e.
domination off the null zero set `{K = 0}` (`hKnull`). -/
theorem wrlctAt_mono_of_eventually_le {W K K' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hWmeas : Measurable W) (hK'meas : Measurable K')
    (hW : ∀ᶠ w in 𝓝 x, 0 ≤ W w)
    (hbound : ∀ᶠ w in 𝓝 x, 0 ≤ K w ∧ K w ≤ K' w)
    (hKnull : LocallyNullZeros K x)
    (hbdd : BddAbove (wLocalAdmissibleExponents W K' x)) :
    wrlctAt W K x ≤ wrlctAt W K' x := by
  have hsub := wLocalAdmissibleExponents_subset_of_eventually_le hWmeas hK'meas hW hbound hKnull
  rcases (wLocalAdmissibleExponents W K x).eq_empty_or_nonempty with hAe | hAne
  · unfold wrlctAt
    rw [hAe, Real.sSup_empty]
    exact Real.sSup_nonneg fun c hc ↦ hc.1
  · exact csSup_le_csSup hbdd hAne hsub

/-- **Object A (weighted ≤).** Weighted ideal-invariance: multiplying the pointwise comparison
`∑ Gᵢ² ≤ C · ∑ Fⱼ²` by the nonnegative weight `W` preserves it, so the weighted RLCTs compare the
same way. The weighted integrand is `W · K^(-c)` (NOT `(W·K)^(-c)`) — its `Real.rpow` junk-`0` comes
from `K^(-c)` at `{K=0}` (independent of `W`), so the guard is `LocallyNullZeros (sumSqFam G)`
(`hGnull`, on `K`, not on `W·K`). Needs `W` and the DENOMINATOR family `F` measurable (`hWmeas`,
`hFmeas` — the RHS integrand `W·(∑Fⱼ²)^(-c)`; the numerator `G`'s measurability is NOT needed for the
`≤`, only for the two-sided `eq`, where the roles swap). The form Object B's CoV consumes. -/
theorem wrlctAt_sumSqFam_le_of_germRepresents {m p : ℕ} {W : (Fin n → ℝ) → ℝ}
    {G : Fin p → (Fin n → ℝ) → ℝ} {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hWmeas : Measurable W) (hFmeas : ∀ j, Measurable (F j))
    (hW : ∀ᶠ w in 𝓝 x, 0 ≤ W w) (h : GermRepresents G F x)
    (hGnull : LocallyNullZeros (sumSqFam G) x)
    (hbdd : BddAbove (wLocalAdmissibleExponents W (sumSqFam F) x)) :
    wrlctAt W (sumSqFam G) x ≤ wrlctAt W (sumSqFam F) x := by
  obtain ⟨C, hC0, hCbound⟩ := eventually_sumSqFam_le_of_germRepresents h
  have hC'pos : (0 : ℝ) < C + 1 := by linarith
  have hsumFmeas : Measurable (sumSqFam F) :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hFmeas i).pow_const 2
  have hbound' : ∀ᶠ w in 𝓝 x,
      0 ≤ sumSqFam G w ∧ sumSqFam G w ≤ (C + 1) * sumSqFam F w := by
    filter_upwards [hCbound] with w hw
    exact ⟨sumSqFam_nonneg G w,
      hw.trans (mul_le_mul_of_nonneg_right (by linarith) (sumSqFam_nonneg F w))⟩
  have hbdd' : BddAbove (wLocalAdmissibleExponents W (fun w ↦ (C + 1) * sumSqFam F w) x) := by
    rw [wLocalAdmissibleExponents_const_mul hC'pos]; exact hbdd
  have hmono := wrlctAt_mono_of_eventually_le hWmeas (hsumFmeas.const_mul (C + 1)) hW
    hbound' hGnull hbdd'
  rwa [wrlctAt_const_mul hC'pos] at hmono

/-- **Object A (weighted =), two-sided — the form Object B's value consumes.** With coinciding germ
ideals (`hGF`/`hFG`), both sum-of-squares zero sets locally null, and `W`/families measurable, the
weighted RLCTs are equal: `le_antisymm` of the two weighted junk-guarded containments. Object B has
both `hideal_fwd`/`hideal_bwd`, so the engine rides this TRUE two-sided form (not a one-sided
assumption). -/
theorem wrlctAt_sumSqFam_eq_of_germ_eq {m p : ℕ} {W : (Fin n → ℝ) → ℝ}
    {G : Fin p → (Fin n → ℝ) → ℝ} {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hWmeas : Measurable W) (hFmeas : ∀ j, Measurable (F j)) (hGmeas : ∀ i, Measurable (G i))
    (hW : ∀ᶠ w in 𝓝 x, 0 ≤ W w)
    (hGnull : LocallyNullZeros (sumSqFam G) x) (hFnull : LocallyNullZeros (sumSqFam F) x)
    (hGbdd : BddAbove (wLocalAdmissibleExponents W (sumSqFam G) x))
    (hFbdd : BddAbove (wLocalAdmissibleExponents W (sumSqFam F) x))
    (hGF : GermRepresents G F x) (hFG : GermRepresents F G x) :
    wrlctAt W (sumSqFam G) x = wrlctAt W (sumSqFam F) x :=
  -- map: A-weighted-two-sided (le_antisymm of both weighted junk-guarded containments)
  le_antisymm (wrlctAt_sumSqFam_le_of_germRepresents hWmeas hFmeas hW hGF hGnull hFbdd)
    (wrlctAt_sumSqFam_le_of_germRepresents hWmeas hGmeas hW hFG hFnull hGbdd)

/-- **Object A (weighted, set form) — the weighted admissible sets coincide under equal germ ideals.**
The bdd-free strengthening of `wrlctAt_sumSqFam_eq_of_germ_eq`: from the two-way domination the two
weighted admissible-exponent sets are EQUAL (each is squeezed into a positive-constant multiple of
the other, which leaves the set unchanged). Consumers get the `wrlctAt` equality by `sSup`-congruence
and `BddAbove` transfer for free — no boundedness hypothesis needed. -/
theorem wLocalAdmissibleExponents_sumSqFam_eq_of_germ_eq {m p : ℕ} {W : (Fin n → ℝ) → ℝ}
    {G : Fin p → (Fin n → ℝ) → ℝ} {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hWmeas : Measurable W) (hFmeas : ∀ j, Measurable (F j)) (hGmeas : ∀ i, Measurable (G i))
    (hW : ∀ᶠ w in 𝓝 x, 0 ≤ W w)
    (hGnull : LocallyNullZeros (sumSqFam G) x) (hFnull : LocallyNullZeros (sumSqFam F) x)
    (hGF : GermRepresents G F x) (hFG : GermRepresents F G x) :
    wLocalAdmissibleExponents W (sumSqFam G) x = wLocalAdmissibleExponents W (sumSqFam F) x := by
  have hsumGmeas : Measurable (sumSqFam G) :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hGmeas i).pow_const 2
  have hsumFmeas : Measurable (sumSqFam F) :=
    Finset.measurable_sum Finset.univ fun j _ ↦ (hFmeas j).pow_const 2
  apply Set.Subset.antisymm
  · obtain ⟨C, hC0, hCbound⟩ := eventually_sumSqFam_le_of_germRepresents hGF
    have hC'pos : (0 : ℝ) < C + 1 := by linarith
    have hbound' : ∀ᶠ w in 𝓝 x,
        0 ≤ sumSqFam G w ∧ sumSqFam G w ≤ (C + 1) * sumSqFam F w := by
      filter_upwards [hCbound] with w hw
      exact ⟨sumSqFam_nonneg G w,
        hw.trans (mul_le_mul_of_nonneg_right (by linarith) (sumSqFam_nonneg F w))⟩
    have hsub := wLocalAdmissibleExponents_subset_of_eventually_le hWmeas
      (hsumFmeas.const_mul (C + 1)) hW hbound' hGnull
    rwa [wLocalAdmissibleExponents_const_mul hC'pos] at hsub
  · obtain ⟨C, hC0, hCbound⟩ := eventually_sumSqFam_le_of_germRepresents hFG
    have hC'pos : (0 : ℝ) < C + 1 := by linarith
    have hbound' : ∀ᶠ w in 𝓝 x,
        0 ≤ sumSqFam F w ∧ sumSqFam F w ≤ (C + 1) * sumSqFam G w := by
      filter_upwards [hCbound] with w hw
      exact ⟨sumSqFam_nonneg F w,
        hw.trans (mul_le_mul_of_nonneg_right (by linarith) (sumSqFam_nonneg G w))⟩
    have hsub := wLocalAdmissibleExponents_subset_of_eventually_le hWmeas
      (hsumGmeas.const_mul (C + 1)) hW hbound' hFnull
    rwa [wLocalAdmissibleExponents_const_mul hC'pos] at hsub

end DLNFibre.Core.Aoyagi
