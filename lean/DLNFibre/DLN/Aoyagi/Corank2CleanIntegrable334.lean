import DLNFibre.DLN.Aoyagi.Corank2CleanHentry334
import DLNFibre.DLN.Aoyagi.Corank2NativeJac334
import DLNFibre.DLN.Aoyagi.LeafChartWire
import DLNFibre.Core.Aoyagi.SandwichCover

/-!
# `DLN.Aoyagi.Corank2CleanIntegrable334` — the CLEAN-144 per-chart `_hint` (discharge (b))

The clean branch of the (3,3,4) V-lower headline's per-chart integrability obligation. For a CLEAN
leaf `c` (`IsClean c`), the born-native chart exposes ONE `coreGen` entry (index `k0 c`) as the
pivot-cross survivor monomial `∏_d w^{ek₀ c d}` EXACTLY (`clean_hentry`), so the pulled-back loss
dominates that monomial's square GLOBALLY (`Finset.single_le_sum`). The Jacobian is a single
monomial (`hjac_gFin`, unit ≡ 1) with binding exponents `≥ 7`, so the boxed monomial threshold is
`≥ 4`, and the Core sandwich engine `integrableAtFilter_of_sandwich` makes every `cc < 4`
admissible for the loss against the Jacobian weight — the `_hint`-shaped `IntegrableAtFilter` the
step-6 spine `rlctAt_coreGen334_ge_four_of_perchart_integrable` consumes on the clean charts.

The statement is parametrised over a generic chart `g'` (fed the entry-equality `hentry` and the
Jacobian collapse `hjac'`), so it applies both to `gFin c` directly and to a `∘ id`-folded clean
chart `gFin c ∘ id`.

## Scope (honest)
- IN: the clean-branch `_hint` from the survivor entry-equality + the monomial-threshold `≥ 4`.
- OUT: the over-vanishing-144 `_hint` (the folded-chart bridge, a separate feeder); the cover /
  area-formula fields / assembly (the controller's integration).
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.NativeJac334
open DLNFibre.DLN.Aoyagi.CleanHentry334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.CleanIntegrable334

/-! ## §1 — the monomial threshold is `≥ 4` on the clean charts -/

/-- **Every binding axis of `ek₀ c` carries Jacobian exponent `≥ 7`.** The binding axes are the
pivot-cross `{p1, p2}` (`bindingAxes_ek₀`); `jacExp_pivot1 = 8` and `jacExp_pivot2_ge ≥ 7`. -/
theorem jacFin_ge_seven_on_binding (c : Fin numCharts) (d : Fin 21)
    (hd : d ∈ bindingAxes (ek₀ c)) : 7 ≤ jacFin c d := by
  rw [bindingAxes_ek₀] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h
  · subst h
    have : jacFin c (pivot1 c) = 8 := by
      simp only [jacFin, pivot1]; exact jacExp_pivot1 (idxEquiv c)
    omega
  · subst h
    simp only [jacFin, pivot2]; exact jacExp_pivot2_ge (idxEquiv c)

/-- **The clean-chart boxed monomial threshold is `≥ 4`.** `ek₀ c = 1` on each binding axis
(`hunit_mult`) and `jacFin c ≥ 7` there, so each ratio `(jac_d + 1)/(2·1) ≥ 4`, hence their
`inf'`. -/
theorem four_le_monomialThreshold (c : Fin numCharts) :
    (4 : ℝ) ≤ monomialThreshold (ek₀ c) (jacFin c) (NativeValue334.hbind c) := by
  unfold monomialThreshold
  refine Finset.le_inf' (NativeValue334.hbind c) _ (fun d hd => ?_)
  have h1 : ek₀ c d = 1 := hunit_mult c d hd
  have h7 : 7 ≤ jacFin c d := jacFin_ge_seven_on_binding c d hd
  have hcast : ((ek₀ c d : ℕ) : ℝ) = 1 := by rw [h1]; norm_num
  have h7R : (7 : ℝ) ≤ (jacFin c d : ℝ) := by exact_mod_cast h7
  rw [hcast, mul_one]
  linarith

/-! ## §2 — the clean-branch per-chart `_hint` -/

/-- **The clean-branch per-chart `_hint`, generic chart form.** Given a chart `g'` (measurable)
whose `k0 c`-indexed `coreGen` entry is the pivot-cross survivor monomial (`hentry`) and whose
Jacobian is the single monomial `jacWeight (jacFin c)` (`hjac'`, unit ≡ 1), the weighted pulled-back
loss `|jacDet g'| · (∑ᵢ (coreGenᵢ ∘ g')²)^{-cc}` is integrable near any point `p`, for every
`cc ∈ [0, 4)`. The survivor entry-equality gives the sandwich `monomial² ≤ loss` (globally,
`Finset.single_le_sum`); the boxed threshold is `≥ 4` (`four_le_monomialThreshold`), so
`integrableAtFilter_of_sandwich` applies. -/
theorem clean_hint_of_entry (c : Fin numCharts)
    (g' : (Fin 21 → ℝ) → (Fin 21 → ℝ)) (hg'meas : Measurable g')
    (hentry : ∀ w, coreGen dvec eWrap (k0 c) (g' w) = ∏ d, (w d) ^ (ek₀ c d))
    (hjac' : ∀ u, |jacDet g' u| = jacWeight (jacFin c) u)
    (p : Fin 21 → ℝ) (cc : ℝ) (hcc : cc ∈ Set.Ico (0 : ℝ) 4) :
    IntegrableAtFilter
      (fun u ↦ |jacDet g' u|
        * negPow (sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ g')) cc u) (𝓝 p) := by
  have hWmeas : Measurable (fun u ↦ |jacDet g' u|) :=
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ g')).abs
  have hLmeas : Measurable (sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ g')) := by
    unfold sumSqFam
    exact Finset.measurable_sum _
      (fun i _ ↦ (((continuous_coreGen dvec eWrap i).measurable).comp hg'meas).pow_const 2)
  refine integrableAtFilter_of_sandwich
    (W := fun u ↦ |jacDet g' u|) (L := sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ g'))
    (e := fun _ : Fin 1 ↦ ek₀ c) (jac := jacFin c) (k₀ := (0 : Fin 1))
    (um := fun _ ↦ (1 : ℝ)) (cst := (1 : ℝ)) (p := p) (cc := cc)
    (fun k d ↦ le_refl _) (NativeValue334.hbind c)
    (lt_of_lt_of_le hcc.2 (four_le_monomialThreshold c)) hcc.1 one_pos
    continuousAt_const one_ne_zero measurable_const
    (Filter.Eventually.of_forall (fun u ↦ show |jacDet g' u| = jacWeight (jacFin c) u * (1 : ℝ)
      from by rw [hjac' u, mul_one]))
    hWmeas (Filter.Eventually.of_forall (fun u ↦ abs_nonneg _)) hLmeas ?_
  -- the sandwich: `1 · (∏ w^{ek₀})² = (coreGen (k0 c) (g' w))² ≤ loss` (single_le_sum).
  refine Filter.Eventually.of_forall (fun u ↦ ?_)
  have hcollapse : sumSqFam (monomialFam (fun _ : Fin 1 ↦ ek₀ c)) u
      = (∏ d, (u d) ^ (ek₀ c d)) ^ 2 := by
    simp [sumSqFam, monomialFam]
  have hLu : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ g') u
      = ∑ i, (coreGen dvec eWrap i (g' u)) ^ 2 := by
    simp only [sumSqFam, Function.comp_apply]
  refine ⟨by rw [one_mul, hcollapse]; exact sq_nonneg _, ?_⟩
  rw [one_mul, hcollapse, hLu]
  calc (∏ d, (u d) ^ (ek₀ c d)) ^ 2
      = (coreGen dvec eWrap (k0 c) (g' u)) ^ 2 := by rw [hentry u]
    _ ≤ ∑ i, (coreGen dvec eWrap i (g' u)) ^ 2 :=
        Finset.single_le_sum (f := fun i ↦ (coreGen dvec eWrap i (g' u)) ^ 2)
          (fun i _ ↦ sq_nonneg _) (Finset.mem_univ (k0 c))

/-- **The clean-branch per-chart `_hint` for `gFin c`.** Instantiates `clean_hint_of_entry` at the
whole-conjugate leaf chart `gFin c`: `hentry` is `clean_hentry` (the CLEAN-144 survivor equality),
`hjac'` is `hjac_gFin` with the unit `≡ 1` collapsed (`|unitFin| = 1`). -/
theorem clean_hint (c : Fin numCharts) (hc : IsClean c)
    (p : Fin 21 → ℝ) (cc : ℝ) (hcc : cc ∈ Set.Ico (0 : ℝ) 4) :
    IntegrableAtFilter
      (fun u ↦ |jacDet (gFin c) u|
        * negPow (sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ gFin c)) cc u) (𝓝 p) :=
  clean_hint_of_entry c (gFin c) (differentiable_gFin c).continuous.measurable
    (clean_hentry c hc)
    (fun u ↦ by rw [hjac_gFin c u]; simp [unitFin]) p cc hcc

-- Forced axiom gate: the clean-branch `_hint` rests only on the clean-three foundational axioms.
#assert_banked_clean_batch [four_le_monomialThreshold, clean_hint_of_entry, clean_hint]

end DLNFibre.DLN.Aoyagi.CleanIntegrable334
