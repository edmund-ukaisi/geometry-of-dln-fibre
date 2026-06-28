import DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurFiring` — the generic per-corank `SchurRecStep` firing (SKELETON)

The arbitrary-corank generalisation of the validated corank-3 firing (`RouteMSchurCorank3`), producing
`schurRecStep_four : SchurRecStep 4 schurLambda` — the SOLE remaining R1-UPPER input to
`schurGen_lt_top_modulo_recStep`.

The firing dispatches on the corank `r` (numerically validated, Codex-confirmed REACHABLE-PLUMBING):
* `r = 0` — vacuous (`c' < schurLambda 0 = 0` contradicts `0 < c'`);
* `r = 1` — the Morse leaf (`c' < schurLambda 1 = 1/2`): a 1-D radial a-axis divisor in `Δ₀₀` times a
  `Fin 4` Morse block in `S`;
* `r = 2` — the corank-2 base, direct from `core_schur2_lt_top` (general `T`);
* `r ≥ 3` — the GENUINE firing: flatten `Δ → Fin (r²)`, `recStep` `r²`-chart cover, per-chart radial
  pull-out (`|det| = |y_p|^{r²−1}`, `radialDelta_loss_factor`), `piFinSuccAbove` splits the pivot axis
  (a-axis divisor finite for `c' < r²/2`) from the `r²−1` ratios; the ratio residual `∫_z innerS(c',R)`
  finite via N2b (`j = 1`) → shifted `Fin 4` Morse peel (threshold `2`, needs `c' > 2`) → the residual at
  `c'' = c' − 2 ∈ (0, schurLambda (r−1))`, translation-dominated `M22 ↦ Sc` into a free `(r−1)×(r−1)` box
  and closed by the ABSTRACT lower IH `SchurLowerIH 4 schurLambda r` at corank `r − 1`. The subcritical
  `c' ≤ 2` case dominates `F^{−c'} ≤ 1 + F^{−3}` and reduces to the `c'' = 3` mid case (`3 ∈ (2, λ_r)` for
  `r ≥ 3`).

The decoupling (genm-recstep verified): the firing invokes the lower-corank IH ABSTRACTLY (the
`SchurLowerIH` hypothesis), NOT the concrete general-T corank-3 core — so this file does not depend on a
concrete general-T `core_schur3`.

## S2-hygiene
S2-FREE: the radial Jacobian dets, the shifted Morse peel (`radial_ball_iff`-based), the translation
dominations (measure-preserving), the corank-2 base (S2-free). No `monomial_rlct`, no new axiom.

STATUS: SKELETON — sub-lemmas are `sorry`, filled in dependency order. The deferred content is named in each
lemma, never hidden in the wrapper.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The r = 1 Morse-leaf base -/

/-- The corank-1 loss core is the product `frobSq (Δ·S) = (Δ₀₀)²·∑ⱼ (S₀ⱼ)²` (one row, one inner index). -/
theorem frobSq_one_eq (Δ : Fin 1 → Fin 1 → ℝ) (S : Fin 1 → Fin 4 → ℝ) :
    frobSq (rmatMul Δ S) = (Δ 0 0) ^ 2 * ∑ j, (S 0 j) ^ 2 := by
  unfold frobSq rmatMul
  rw [Fin.sum_univ_one, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fin.sum_univ_one]; ring

/-- The corank-1 `Δ`-axis divisor `∫_{Δ∈matBox 1 1 T} ((Δ₀₀)²)^{−c'} < ⊤` for `2c' < 1`. The single
matrix coordinate reindexes to `[−T,T]` (`funUnique` twice), and `((·)²)^{−c'} = |·|^{−2c'}` is the
1-D monomial divisor `abs_rpow_lintegral_Icc_lt_top` (exponent `−2c' > −1`). -/
theorem schurOne_delta_divisor_lt_top (c' : ℝ) (hc' : c' < 1 / 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ Δ in matBox 1 1 T, ENNReal.ofReal (((Δ 0 0) ^ 2) ^ (-c'))) < ⊤ := by
  -- reindex (Fin 1 → Fin 1 → ℝ) ≃ᵐ ℝ via funUnique twice; matBox 1 1 T ↦ Icc (-T) T
  set e : (Fin 1 → Fin 1 → ℝ) ≃ᵐ ℝ :=
    (MeasurableEquiv.funUnique (Fin 1) (Fin 1 → ℝ)).trans (MeasurableEquiv.funUnique (Fin 1) ℝ)
    with he
  have hmp : MeasurePreserving e (volume : Measure (Fin 1 → Fin 1 → ℝ)) (volume : Measure ℝ) :=
    (measurePreserving_funUnique (volume : Measure (Fin 1 → ℝ)) (Fin 1)).trans
      (measurePreserving_funUnique (volume : Measure ℝ) (Fin 1))
  have hpre : matBox 1 1 T = e ⁻¹' (Set.Icc (-T) T) := by
    ext Δ
    simp only [matBox, Set.mem_setOf_eq, Set.mem_preimage, he, MeasurableEquiv.trans_apply,
      MeasurableEquiv.funUnique_apply, Set.mem_Icc]
    constructor
    · intro h; exact Set.mem_Icc.1 (h 0 0)
    · intro h i k
      rw [show i = 0 from Subsingleton.elim _ _, show k = 0 from Subsingleton.elim _ _]
      exact Set.mem_Icc.2 h
  rw [hpre]
  have key := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun a => ENNReal.ofReal ((a ^ 2) ^ (-c'))) (Set.Icc (-T) T)
  rw [show (∫⁻ Δ in e ⁻¹' (Set.Icc (-T) T), ENNReal.ofReal (((Δ 0 0) ^ 2) ^ (-c')))
      = ∫⁻ Δ in e ⁻¹' (Set.Icc (-T) T), ENNReal.ofReal (((e Δ) ^ 2) ^ (-c')) from by
    refine setLIntegral_congr_fun (e.measurable measurableSet_Icc) (fun Δ _ => ?_)
    rfl]
  rw [key]
  -- (a²)^{−c'} = |a|^{−2c'}, exponent > −1
  have hcongr : ∀ a : ℝ, ENNReal.ofReal ((a ^ 2) ^ (-c')) = ENNReal.ofReal (|a| ^ (-2 * c')) := by
    intro a
    congr 1
    rw [show (a ^ 2 : ℝ) = |a| ^ (2 : ℕ) from (sq_abs a).symm,
      ← Real.rpow_natCast (|a|) 2, ← Real.rpow_mul (abs_nonneg a)]
    congr 1; push_cast; ring
  rw [lintegral_congr hcongr]
  exact abs_rpow_lintegral_Icc_lt_top T hT (-2 * c') (by linarith)

/-- The corank-1 Morse block `∫_{S∈matBox 1 4 T} (∑ⱼ (S₀ⱼ)²)^{−c'} < ⊤` for `c' < 1/2 < 2`. The single
`S`-row reindexes to `morseBox 4 T`, a `Fin 4` Morse leaf (`radial_morse_dominates_lt_top` with `W = 0`,
threshold `4/2 = 2`). -/
theorem schurOne_morse_lt_top (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 1 / 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ S in matBox 1 4 T, ENNReal.ofReal ((∑ j, (S 0 j) ^ 2) ^ (-c'))) < ⊤ := by
  -- reindex (Fin 1 → Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ); matBox 1 4 T ↦ morseBox 4 T
  set e : (Fin 1 → Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) := MeasurableEquiv.funUnique (Fin 1) (Fin 4 → ℝ) with he
  have hmp : MeasurePreserving e (volume : Measure (Fin 1 → Fin 4 → ℝ))
      (volume : Measure (Fin 4 → ℝ)) :=
    measurePreserving_funUnique (volume : Measure (Fin 4 → ℝ)) (Fin 1)
  have hpre : matBox 1 4 T = e ⁻¹' (morseBox 4 T) := by
    ext S
    simp only [matBox, morseBox, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, he, MeasurableEquiv.funUnique_apply]
    constructor
    · intro h j; exact h 0 j
    · intro h i k; rw [show i = 0 from Subsingleton.elim _ _]; exact h k
  rw [hpre]
  have key := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun P => ENNReal.ofReal ((∑ j, (P j) ^ 2) ^ (-c'))) (morseBox 4 T)
  rw [show (∫⁻ S in e ⁻¹' (morseBox 4 T), ENNReal.ofReal ((∑ j, (S 0 j) ^ 2) ^ (-c')))
      = ∫⁻ S in e ⁻¹' (morseBox 4 T), ENNReal.ofReal ((∑ j, ((e S) j) ^ 2) ^ (-c')) from by
    refine setLIntegral_congr_fun (e.measurable (morseBox_measurableSet 4 T)) (fun S _ => ?_)
    rfl]
  rw [key]
  -- a Fin 4 = Fin (3+1) Morse leaf with W = 0; threshold (3+1)/2 = 2 > c'
  have hmorse := radial_morse_dominates_lt_top (m := 3) (k := 0) c' (by norm_num; linarith)
    (le_of_lt hc0) T hT (fun _ : Fin 0 → ℝ => (0 : ℝ)) (fun _ => le_refl 0) measurable_const
  have hk0 : (∫⁻ _z in morseBox 0 T, ∫⁻ P in morseBox (3 + 1) T,
      ENNReal.ofReal ((∑ i, (P i) ^ 2 + (0 : ℝ)) ^ (-c'))) < ⊤ :=
    lt_of_le_of_lt hmorse (ENNReal.mul_lt_top (Kbound_lt_top 3 T hT c' (by norm_num; linarith))
      (morseBox_volume_lt_top 0 T))
  -- morseBox 0 T = {pt} has volume 1; the z-integral collapses to the single P-integral
  rw [show (morseBox 0 T) = (Set.univ : Set (Fin 0 → ℝ)) from by
    ext z; simp [morseBox, Set.eq_univ_iff_forall]] at hk0
  rw [setLIntegral_univ] at hk0
  have hconst : (∫⁻ _z : Fin 0 → ℝ, ∫⁻ P in morseBox (3 + 1) T,
      ENNReal.ofReal ((∑ i, (P i) ^ 2 + (0 : ℝ)) ^ (-c')))
      = (∫⁻ P in morseBox (3 + 1) T,
          ENNReal.ofReal ((∑ i, (P i) ^ 2 + (0 : ℝ)) ^ (-c'))) * volume (Set.univ : Set (Fin 0 → ℝ)) := by
    rw [lintegral_const]
  rw [hconst, show volume (Set.univ : Set (Fin 0 → ℝ)) = 1 from by simp, mul_one] at hk0
  refine lt_of_le_of_lt (le_of_eq ?_) hk0
  refine lintegral_congr (fun P => ?_)
  simp [add_zero]

/-- **The corank-1 Morse-leaf base.** `SchurCore 4 1 c' T` for `0 < c' < 1/2`: the `1×1` `Δ`-block gives
`frobSq (Δ·S) = Δ₀₀²·∑ⱼ (S₀ⱼ)²`, a product of a 1-D radial a-axis divisor in `Δ₀₀` (`|Δ₀₀|^{−2c'}`,
integrable since `2c' < 1`) and a `Fin 4` Morse block in `S` (finite since `c' < 1/2 < 2`). -/
theorem schurCore4_one (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 1 / 2) (T : ℝ) (hT : 0 < T) :
    SchurCore 4 1 c' T := by
  rw [SchurCore]
  -- pointwise: frobSq(Δ·S)^{−c'} = ((Δ₀₀)²)^{−c'} · (∑S₀ⱼ²)^{−c'}
  have hpt : ∀ Δ : Fin 1 → Fin 1 → ℝ, ∀ S : Fin 1 → Fin 4 → ℝ,
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'))
        = ENNReal.ofReal (((Δ 0 0) ^ 2) ^ (-c'))
          * ENNReal.ofReal ((∑ j, (S 0 j) ^ 2) ^ (-c')) := by
    intro Δ S
    rw [frobSq_one_eq Δ S, Real.mul_rpow (by positivity) (by positivity),
      ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  -- inner S-integral pulls the Δ-factor out, then the constant S-integral pulls out of ∫_Δ
  set CS : ℝ≥0∞ := ∫⁻ S in matBox 1 4 T, ENNReal.ofReal ((∑ j, (S 0 j) ^ 2) ^ (-c')) with hCS
  have hinner : ∀ Δ : Fin 1 → Fin 1 → ℝ,
      (∫⁻ S in matBox 1 4 T, ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')))
        = ENNReal.ofReal (((Δ 0 0) ^ 2) ^ (-c')) * CS := by
    intro Δ
    rw [lintegral_congr (hpt Δ), hCS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_congr hinner, lintegral_mul_const' _ _ (schurOne_morse_lt_top c' hc0 hc' T hT).ne]
  exact ENNReal.mul_lt_top (schurOne_delta_divisor_lt_top c' hc' T hT)
    (schurOne_morse_lt_top c' hc0 hc' T hT)

/-! ## The generic outer radial-Δ `r²`-chart cover (mirror of corank-3 `matToFlat3`/`gFlat3_*`) -/

/-- The generic matrix flatten `matToFlatG r : (Fin r → Fin r → ℝ) ≃ᵐ (Fin (r*r) → ℝ)` (uncurry + the
`Fin r × Fin r ≃ Fin (r·r)` index reindex). -/
noncomputable def matToFlatG (r : ℕ) : (Fin r → Fin r → ℝ) ≃ᵐ (Fin (r * r) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin r) (_ : Fin r) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin r) (Fin r)).trans finProdFinEquiv) (MeasurableEquiv.refl ℝ))

theorem measurePreserving_matToFlatG (r : ℕ) :
    MeasurePreserving (matToFlatG r) (volume : Measure (Fin r → Fin r → ℝ))
      (volume : Measure (Fin (r * r) → ℝ)) := by
  unfold matToFlatG
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin r) (Fin r)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin r) (_ : Fin r) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry (fun (_ : Fin r) (_ : Fin r) => ℝ))

/-- The flattened `Δ`-box on the `Fin (r*r)` carrier: `[−T,T]^{r²}`. -/
def flatBoxG (r : ℕ) (T : ℝ) : Set (Fin (r * r) → ℝ) := {y | ∀ i, y i ∈ Set.Icc (-T) T}

theorem flatBoxG_measurableSet (r : ℕ) (T : ℝ) : MeasurableSet (flatBoxG r T) := by
  rw [flatBoxG, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) measurableSet_Icc)

/-- `matBox r r T = matToFlatG r ⁻¹' flatBoxG r T`. -/
theorem matBoxG_flatBox_preimage (r : ℕ) (T : ℝ) :
    matBox r r T = matToFlatG r ⁻¹' flatBoxG r T := by
  ext Δ
  simp only [matBox, flatBoxG, Set.mem_setOf_eq, Set.mem_preimage]
  set e : (Σ _ : Fin r, Fin r) ≃ Fin (r * r) :=
    (Equiv.sigmaEquivProd (Fin r) (Fin r)).trans finProdFinEquiv with he
  have hcoord : ∀ i : Fin (r * r), (matToFlatG r Δ) i = Δ (e.symm i).1 (e.symm i).2 := fun i => rfl
  constructor
  · intro h i; rw [hcoord i]; exact h (e.symm i).1 (e.symm i).2
  · intro h k j
    have := h (e ⟨k, j⟩)
    rw [hcoord (e ⟨k, j⟩), Equiv.symm_apply_apply] at this
    exact this

/-- The flat-`Δ` cover integrand: `gFlatG c' T y = ∫_{S∈box r 4} frobSq(rmatMul (matToFlatG.symm y) S)^{−c'}`. -/
noncomputable def gFlatG (r : ℕ) (c' : ℝ) (T : ℝ) (y : Fin (r * r) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox r 4 T,
    ENNReal.ofReal ((frobSq (rmatMul ((matToFlatG r).symm y) S)) ^ (-c'))

/-- The `Δ`-outer integral reindexes to the flat `gFlatG` integral over `flatBoxG`. -/
theorem matBoxG_outer_flat (r : ℕ) (c' : ℝ) (T : ℝ) :
    (∫⁻ Δ in matBox r r T, ∫⁻ S in matBox r 4 T,
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')))
      = ∫⁻ y in flatBoxG r T, gFlatG r c' T y := by
  have hmp := measurePreserving_matToFlatG r
  have hcomp := hmp.setLIntegral_comp_preimage_emb (matToFlatG r).measurableEmbedding
    (gFlatG r c' T) (flatBoxG r T)
  rw [matBoxG_flatBox_preimage, ← hcomp]
  refine setLIntegral_congr_fun ((matToFlatG r).measurable (flatBoxG_measurableSet r T))
    (fun Δ _ => ?_)
  rw [gFlatG, MeasurableEquiv.symm_apply_apply]

/-- The cover-to-sum on the `Fin (r*r)` flat carrier (`recStep`, the `r²`-entry argmax cover). Needs
`0 < r` for a pivot to exist (`r ≥ 1` since `r ≥ 3` in the firing). -/
theorem gFlatG_cover_sum (r : ℕ) (hr : 0 < r * r) (c' : ℝ) (T : ℝ) :
    (∫⁻ y in flatBoxG r T, gFlatG r c' T y)
      = ∑ p ∈ (Finset.univ : Finset (Fin (r * r))),
          ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (r * r))) p \ pivotZeroOn p,
            ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) p y).det|
              * (flatBoxG r T).indicator (gFlatG r c' T) (pivotBlowupOn
                  (Finset.univ : Finset (Fin (r * r))) p y) :=
  recStep (Finset.univ : Finset (Fin (r * r))) ⟨0, hr⟩ (Finset.mem_univ _)
    (flatBoxG r T) (flatBoxG_measurableSet r T) (gFlatG r c' T)

/-- The unflattened angular matrix on chart `p`: `RmatG p y` is the `r×r` matrix with `R_p = 1`,
`R_k = y_k` (`k ≠ p`). -/
noncomputable def RmatG (r : ℕ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ) : Fin r → Fin r → ℝ :=
  (matToFlatG r).symm (fun i => if i = p then 1 else y i)

/-- **The radial pull-out** (N1 degree-2 homogeneity): `gFlatG c' T (blowup) =
∫_S ((y p)²·frobSq(RmatG·S))^{−c'}`. -/
theorem gFlatG_blowup_radial (r : ℕ) (c' : ℝ) (T : ℝ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ) :
    gFlatG r c' T (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y)
      = ∫⁻ S in matBox r 4 T,
          ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (RmatG r p y) S)) ^ (-c')) := by
  unfold gFlatG RmatG
  refine lintegral_congr (fun S => ?_)
  congr 1
  have hbl : (matToFlatG r).symm (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y)
      = fun a b => (y p) * ((matToFlatG r).symm (fun i => if i = p then 1 else y i)) a b := by
    funext a b
    show (matToFlatG r).symm (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y) a b = _
    rw [show pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y
        = (fun i => (y p) * (if i = p then 1 else y i)) from by
      funext i; unfold pivotBlowupOn
      by_cases hi : i = p
      · subst hi; simp
      · simp [hi]]
    rfl
  rw [hbl, radialDelta_loss_factor (y p) ((matToFlatG r).symm (fun i => if i = p then 1 else y i)) S]

/-! ## The generic firing at corank r ≥ 3

The firing's heart is NOT a fixed-`R` inner-`S` finiteness (that is FALSE — `∫_S frobSq (R·S)^{−c'}`
diverges when `R` is rank-deficient, e.g. `Sc` singular). It is the JOINT RATIO-RESIDUAL `∫_z ∫_S
frobSq (R(z)·S)^{−c'}` over the angular ratios `z` AND `S`: integrating over `z` is what carries the free
`M22` block the lower IH consumes (the corank-3 `schurInner3_ratiofin` likewise integrates over `z`, not a
fixed `R`). The `M22 ↦ Sc` carving identifies the `(r−1)²` ratio coordinates forming `M22` and translation-
dominates `Sc` into the free `(r−1)×(r−1)` IH box. -/

/-- The inner angular `S`-integral at the angular matrix `RmatG r p y` (pivot `1`, `|entries| ≤ 1` on the
ratio chart): `innerSGen r c' T p y = ∫_{S∈matBox r 4 T} frobSq (RmatG r p y · S)^{−c'}`. -/
noncomputable def innerSGen (r : ℕ) (c' : ℝ) (T : ℝ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox r 4 T, ENNReal.ofReal ((frobSq (rmatMul (RmatG r p y) S)) ^ (-c'))

/-- **The pivot-axis ↔ ratios reshape** `piRatioG r N hN p : (Fin (r*r) → ℝ) ≃ᵐ ℝ × (Fin N → ℝ)` (the
`Fin (r*r)`-carrier analogue of `piFinSuccAbove`): reindex `Fin (r*r) ≃ Fin (N+1)` (`finCongr hN`,
`r*r = N+1`), then split off the pivot axis `p`. Measure-preserving (`measurePreserving_piRatioG`). -/
noncomputable def piRatioG (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r)) :
    (Fin (r * r) → ℝ) ≃ᵐ ℝ × (Fin N → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (N + 1) => ℝ) (finCongr hN)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))

theorem measurePreserving_piRatioG (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r)) :
    MeasurePreserving (piRatioG r N hN p) (volume : Measure (Fin (r * r) → ℝ))
      (volume : Measure (ℝ × (Fin N → ℝ))) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (N + 1) => ℝ) (finCongr hN)).trans
    (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))

/-- **The generic ratio-residual (the firing heart, mid case `2 < c' < λ_r`).** The JOINT integral over
the `r²−1` angular ratios `z` (pivot axis set to `0` via `piRatioG`) and `S` is finite for
`2 < c' < λ_r`, `r ≥ 3`: per `z` the angular `RmatG r p ((piRatioG …).symm (0,z))` has pivot `1`,
`|entries| ≤ 1`; N2b (`j = 1`) peels the top `Fin 4` Morse block (threshold `2`), leaving the residual at
`c'' = c' − 2 ∈ (0, λ_{r−1})`; the `M22 ↦ Sc` carving + the lower IH `hIH` close it. The genuinely-new
generic content. `N = r²−1` (so `r * r = N + 1`). -/
theorem schurRatioResidGen_mid (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc2 : 2 < c') (hc' : c' < schurLambda r)
    (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGen r c' T p ((piRatioG r N hN p).symm (0, z)))
      < ⊤ := by
  sorry

/-- **The generic ratio-residual, all `0 < c' < λ_r` (subcritical fold).** Mid case `2 < c'` is
`schurRatioResidGen_mid`; subcritical `c' ≤ 2` dominates `F^{−c'} ≤ 1 + F^{−3}` and reduces to the
`c'' = 3` mid case (`3 ∈ (2, λ_r)` since `λ_r = 2r−2 ≥ 4` for `r ≥ 3`). -/
theorem schurRatioResidGen (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambda r)
    (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGen r c' T p ((piRatioG r N hN p).symm (0, z)))
      < ⊤ := by
  sorry

/-- **The generic per-chart finiteness.** Mirror of `matBox3_chart_lt_top` at generic `r`: the radial
blow-up chart integral (Jacobian `|y p|^{r²−1}`) is finite for `0 < c' < λ_r`, `r ≥ 3`. The
`piFinSuccAbove p` MP + Tonelli factor the pivot axis (a-axis divisor finite for `c' < r²/2`, holds since
`c' < λ_r ≤ r²/2`) from the `r²−1` ratios; the ratio residual is `schurRatioResidGen_mid` (subcritical
`c' ≤ 2` folded by `ofReal_rpow…` domination to the `c'' = 3` mid case). -/
theorem schur_matBoxG_chart_lt_top (r : ℕ) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambda r)
    (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (r * r))) p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) p y).det|
          * (flatBoxG r T).indicator (gFlatG r c' T) (pivotBlowupOn
              (Finset.univ : Finset (Fin (r * r))) p y)
      < ⊤ := by
  sorry

/-- **The generic firing at corank r ≥ 3.** `SchurCore 4 r c' T` for `0 < c' < schurLambda r`: flatten
`Δ → Fin (r²)`, `recStep` `r²`-chart cover, each chart finite (`schur_matBoxG_chart_lt_top`), summed by
`ENNReal.sum_lt_top`. -/
theorem schurCoreGen_firing (r : ℕ) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambda r) (T : ℝ) (hT : 0 < T) :
    SchurCore 4 r c' T := by
  rw [SchurCore, matBoxG_outer_flat r c' T,
    gFlatG_cover_sum r (by positivity) c' T]
  exact ENNReal.sum_lt_top.2 (fun p _ => schur_matBoxG_chart_lt_top r hr hIH c' hc0 hc' p T hT)

/-! ## The dispatch: `SchurRecStep 4 schurLambda` -/

/-- **The generic per-corank firing.** `SchurRecStep 4 schurLambda` — the SOLE remaining R1-UPPER input.
Dispatches on `r`: `r = 0` vacuous, `r = 1` Morse leaf (`schurCore4_one`), `r = 2` base
(`schurCore4_two`), `r ≥ 3` the firing (`schurCoreGen_firing`). -/
theorem schurRecStep_four : SchurRecStep 4 schurLambda := by
  intro r _hlam hIH c' hc0 hclt T hT
  match r, hclt, hIH with
  | 0, hclt, _ =>
      exact absurd hclt (by rw [schurLambda_zero]; exact not_lt.2 (le_of_lt hc0))
  | 1, hclt, _ =>
      exact schurCore4_one c' hc0 (by rw [schurLambda_one] at hclt; exact hclt) T hT
  | 2, hclt, _ =>
      exact schurCore4_two c' hc0 (by rw [schurLambda_two] at hclt; exact hclt) T hT
  | (n + 3), hclt, hIH =>
      exact schurCoreGen_firing (n + 3) (by omega) hIH c' hc0 hclt T hT

end DLNFibre.DLN.RLCT
