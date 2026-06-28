import DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral
import DLNFibre.DLN.RLCT.Validate.RadialResidualPower
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet

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

/-! ### Per-chart support (mirror of corank-3 `Rmat3_*` / `innerS3_*` / `flatBox3_blowup_mem_iff`) -/

/-- The matrix↔flat index equiv `eG r : Fin r × Fin r ≃ Fin (r*r)`, matching `matToFlatG`'s index reindex. -/
noncomputable def eG (r : ℕ) : Fin r × Fin r ≃ Fin (r * r) :=
  ((Equiv.sigmaEquivProd (Fin r) (Fin r)).symm).trans
    ((Equiv.sigmaEquivProd (Fin r) (Fin r)).trans finProdFinEquiv)

/-- `RmatG r p y i j = if eG r (i,j) = p then 1 else y (eG r (i,j))` (the unflattened angular matrix). -/
theorem RmatG_entry (r : ℕ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ) (i j : Fin r) :
    RmatG r p y i j = if eG r (i, j) = p then 1 else y (eG r (i, j)) := rfl

/-- The pivot entry of `RmatG r p y` is `1` (at the matrix index `(eG r).symm p`). -/
theorem RmatG_pivot (r : ℕ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ) :
    RmatG r p y ((eG r).symm p).1 ((eG r).symm p).2 = 1 := by
  rw [RmatG_entry, if_pos]
  rw [show (((eG r).symm p).1, ((eG r).symm p).2) = (eG r).symm p from rfl, Equiv.apply_symm_apply]

/-- `|RmatG r p y i j| ≤ 1` on the ratio chart `|y_k| ≤ 1` (`k ≠ p`); pivot entry `= 1`. -/
theorem RmatG_entry_le (r : ℕ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ)
    (hy : ∀ k, k ≠ p → |y k| ≤ 1) (i j : Fin r) : |RmatG r p y i j| ≤ 1 := by
  rw [RmatG_entry]
  by_cases h : eG r (i, j) = p
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; exact hy _ h

/-- `innerSGen` is `y p`-invariant: `RmatG r p y` reads `y i` only for `i ≠ p`. -/
theorem innerSGen_offpivot (r : ℕ) (c' : ℝ) (T : ℝ) (p : Fin (r * r)) (y y' : Fin (r * r) → ℝ)
    (h : ∀ i, i ≠ p → y i = y' i) : innerSGen r c' T p y = innerSGen r c' T p y' := by
  have hR : RmatG r p y = RmatG r p y' := by
    funext i j; rw [RmatG_entry, RmatG_entry]
    by_cases hij : eG r (i, j) = p
    · rw [if_pos hij, if_pos hij]
    · rw [if_neg hij, if_neg hij]; exact h _ hij
  rw [innerSGen, innerSGen, hR]

/-- `frobSq (R·S)` is invariant under a row-perm `σr` of `R` + a simultaneous col-perm `σc` of `R`
(= row-perm of `S`). The generic-`r` analog of `frobSq_rmatMul_perm2`. -/
theorem frobSq_rmatMul_permG {r : ℕ} (R : Fin r → Fin r → ℝ) (S : Fin r → Fin 4 → ℝ)
    (σr σc : Fin r ≃ Fin r) :
    frobSq (rmatMul R S)
      = frobSq (rmatMul (fun a c => R (σr a) (σc c)) (fun k j => S (σc k) j)) := by
  unfold frobSq rmatMul
  rw [← Equiv.sum_comp σr (fun a => ∑ j, (∑ k, R a k * S k j) ^ 2)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  rw [← Equiv.sum_comp σc (fun k => R (σr a) k * S k j)]

/-- The `S` row-permutation change of variables on the symmetric box `matBox r 4 T`: permuting the
`Fin r` row-index of `S` by `σc` is measure-preserving (`piCongrLeft`) and the box is `σc`-invariant.
The generic-`r` analog of `matBox24_rowperm_lintegral`. -/
theorem matBox_rowperm_lintegralG {r : ℕ} (T : ℝ) (σc : Fin r ≃ Fin r)
    (f : (Fin r → Fin 4 → ℝ) → ℝ≥0∞) :
    (∫⁻ S in matBox r 4 T, f S) = ∫⁻ S in matBox r 4 T, f (fun k j => S (σc k) j) := by
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin r => Fin 4 → ℝ) σc with hE
  have hmp : MeasurePreserving E.symm volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin r => Fin 4 → ℝ) σc).symm E
  have hpre : matBox r 4 T = E.symm ⁻¹' (matBox r 4 T) := by
    ext S
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k; exact h (σc i) k
    · intro h i k
      have := h (σc.symm i) k
      rw [show E.symm S (σc.symm i) k = S i k from by
        show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
      exact this
  have key := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding f (matBox r 4 T)
  have hrhs : (∫⁻ S in matBox r 4 T, f (fun k j => S (σc k) j))
      = ∫⁻ S in matBox r 4 T, f (E.symm S) := rfl
  rw [hrhs]
  rw [← hpre] at key
  exact key.symm

/-- `innerSGen r c' T p` is measurable in `y`. -/
theorem measurable_innerSGen (r : ℕ) (c' : ℝ) (T : ℝ) (p : Fin (r * r)) :
    Measurable (innerSGen r c' T p) := by
  unfold innerSGen
  apply Measurable.lintegral_prod_right (f := fun y S =>
    ENNReal.ofReal ((frobSq (rmatMul (RmatG r p y) S)) ^ (-c')))
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  unfold frobSq rmatMul
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  apply Finset.measurable_sum; intro k _
  apply Measurable.mul
  · have hy : Measurable (fun y : Fin (r * r) → ℝ => RmatG r p y i k) := by
      simp only [RmatG_entry]
      by_cases h : eG r (i, k) = p
      · simp only [if_pos h]; exact measurable_const
      · simp only [if_neg h]; exact measurable_pi_apply _
    exact hy.comp measurable_fst
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd)

/-- On the chart, the blown-up point lands in `flatBoxG r T` IFF `|y p| ≤ T`. -/
theorem flatBoxG_blowup_mem_iff (r : ℕ) (T : ℝ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (r * r))) p) :
    pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y ∈ flatBoxG r T ↔ |y p| ≤ T := by
  unfold flatBoxG chartDomOn at *
  simp only [Set.mem_setOf_eq] at *
  constructor
  · intro h
    have hpp := h p
    rw [pivotBlowupOn] at hpp
    simp only [if_pos rfl, Set.mem_Icc] at hpp
    rw [abs_le]; exact hpp
  · intro hp i
    rw [pivotBlowupOn]
    by_cases hi : i = p
    · subst hi; simp only [if_pos rfl, Set.mem_Icc]; rw [abs_le] at hp; exact hp
    · simp only [if_neg hi, Finset.mem_univ, if_true, Set.mem_Icc]
      have hyi : |y i| ≤ 1 := hy i (Finset.mem_univ i) hi
      have hb : |y p * y i| ≤ |y p| := by
        rw [abs_mul]; nlinarith [abs_nonneg (y p), abs_nonneg (y i), abs_nonneg (y p * y i)]
      have hbb : |y p * y i| ≤ T := le_trans hb hp
      rw [abs_le] at hbb; exact hbb

/-- **The pivot-axis ↔ ratios reshape** `piRatioG r N hN p : (Fin (r*r) → ℝ) ≃ᵐ ℝ × (Fin N → ℝ)` (the
`Fin (r*r)`-carrier analogue of `piFinSuccAbove`): reindex `Fin (r*r) ≃ Fin (N+1)` by PRECOMPOSITION
(`arrowCongr'` along `finCongr hN`, the constant-codomain reshape — clean `eq_rec`-free `.symm`), then
split off the pivot axis `p`. Measure-preserving (`measurePreserving_piRatioG`). -/
noncomputable def piRatioG (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r)) :
    (Fin (r * r) → ℝ) ≃ᵐ ℝ × (Fin N → ℝ) :=
  (MeasurableEquiv.arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))

theorem measurePreserving_piRatioG (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r)) :
    MeasurePreserving (piRatioG r N hN p) (volume : Measure (Fin (r * r) → ℝ))
      (volume : Measure (ℝ × (Fin N → ℝ))) := by
  unfold piRatioG
  refine MeasurePreserving.trans ?_
    (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))
  exact volume_preserving_arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)

/-- `(piRatioG r N hN p).symm (a, z) k = (insertNth (finCongr hN p) a z) (finCongr hN k)` — the explicit
read-back (precompose `arrowCongr'.symm` = compose with `finCongr hN`; `piFinSuccAbove.symm = insertNth`). -/
theorem piRatioG_symm_apply (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r))
    (a : ℝ) (z : Fin N → ℝ) (k : Fin (r * r)) :
    (piRatioG r N hN p).symm (a, z) k
      = Fin.insertNthEquiv (fun _ : Fin (N + 1) => ℝ) (finCongr hN p) (a, z) (finCongr hN k) := by
  show (MeasurableEquiv.arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ)).symm
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p)).symm (a, z)) k = _
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

/-- The pivot value of the read-back is `a`. -/
theorem piRatioG_symm_pivot (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r))
    (a : ℝ) (z : Fin N → ℝ) : (piRatioG r N hN p).symm (a, z) p = a := by
  rw [piRatioG_symm_apply]
  simp [Fin.insertNthEquiv, Fin.insertNth_apply_same]

/-- Off the pivot the read-back is `a`-independent: `(piRatioG …).symm (a,z) k = (piRatioG …).symm (a',z) k`
for `k ≠ p` (the `finCongr` images differ, so `insertNth` reads `z` not the pivot slot). -/
theorem piRatioG_symm_offpivot (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r))
    (a a' : ℝ) (z : Fin N → ℝ) (k : Fin (r * r)) (hk : k ≠ p) :
    (piRatioG r N hN p).symm (a, z) k = (piRatioG r N hN p).symm (a', z) k := by
  rw [piRatioG_symm_apply, piRatioG_symm_apply]
  -- finCongr hN k ≠ finCongr hN p, so k decodes via succAbove and insertNth reads z
  have hne : finCongr hN k ≠ finCongr hN p := fun h => hk ((finCongr hN).injective h)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
  rw [← hj]
  simp [Fin.insertNthEquiv, Fin.insertNth_apply_succAbove]

/-- The pivot value of the forward map: `(piRatioG r N hN p y).1 = y p`. -/
theorem piRatioG_apply_fst (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r)) (y : Fin (r * r) → ℝ) :
    (piRatioG r N hN p y).1 = y p := by
  show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))
        ((MeasurableEquiv.arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ)) y)).1 = y p
  simp only [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.coe_mk, Fin.insertNthEquiv]
  rfl

/-- The `j`-th ratio of the forward map: `(piRatioG r N hN p y).2 j = y (the succAbove-decoded index)`. The
decoded index `(finCongr hN).symm ((finCongr hN p).succAbove j) ≠ p` (the ratios omit the pivot). -/
theorem piRatioG_apply_snd (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r)) (y : Fin (r * r) → ℝ)
    (j : Fin N) :
    (piRatioG r N hN p y).2 j = y ((finCongr hN).symm ((finCongr hN p).succAbove j)) := by
  show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (finCongr hN p))
        ((MeasurableEquiv.arrowCongr' (finCongr hN) (MeasurableEquiv.refl ℝ)) y)).2 j = _
  simp only [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.coe_mk, Fin.insertNthEquiv]
  rfl

/-- The decoded ratio index is never the pivot: `(finCongr hN).symm ((finCongr hN p).succAbove j) ≠ p`. -/
theorem piRatioG_ratioIdx_ne (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r)) (j : Fin N) :
    (finCongr hN).symm ((finCongr hN p).succAbove j) ≠ p := by
  intro h
  apply Fin.succAbove_ne (finCongr hN p) j
  have h' : finCongr hN ((finCongr hN).symm ((finCongr hN p).succAbove j)) = finCongr hN p := by
    rw [h]
  rwa [(finCongr hN).apply_symm_apply] at h'

/-- **Pointwise rpow domination** `ofReal(x^{−c'}) ≤ 1 + ofReal(x^{−c''})` for `x ≥ 0`, `0 < c' ≤ c''`
(local copy of `RouteMSchurCorank3.ofReal_rpow_neg_le_one_add`, kept local to avoid coupling the generic
firing to the bespoke corank-3 file). On `x ≥ 1` the LHS `≤ 1`; on `0 < x < 1` the LHS `≤ x^{−c''}`; at
`x = 0` both `0^{neg} = 0`. The subcritical reduction of the `c' ≤ 2` ratio-residual to `c'' = 3`. -/
theorem ofReal_rpow_neg_le_one_addG (x : ℝ) (hx : 0 ≤ x) (c' c'' : ℝ) (hc0 : 0 < c') (hcc : c' ≤ c'') :
    ENNReal.ofReal (x ^ (-c')) ≤ 1 + ENNReal.ofReal (x ^ (-c'')) := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0, Real.zero_rpow (by linarith), ENNReal.ofReal_zero]
    exact zero_le _
  · rcases le_or_gt 1 x with h1 | h1
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_add_right (le_of_eq ENNReal.ofReal_one))
      calc x ^ (-c') ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        _ = 1 := Real.rpow_zero x
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_add_left (le_refl _))
      exact Real.rpow_le_rpow_of_exponent_ge hx0 (le_of_lt h1) (by linarith)

/-! ### The free-core a.e.-positivity (the Morse-peel `w > 0` feed)

The shifted Morse peel `radial_morse_residual_power_le` needs `w = frobSq (Sc·S_bot) > 0`. For the FREE
corank-`m` core (`Δ` a full `m×m` matrix, `S` an `m×4` matrix), `frobSq (Δ·S) > 0` a.e.: the entry
`(Δ·S) 0 0 = ∑ₖ Δ(0,k)·S(k,0)` is a nonzero `MvPolynomial` in the joint coords (witness `Δ(0,0)=S(0,0)=1`,
rest `0`), so its zero set is null (`MvPolynomial.ae_eval_ne_zero`), and `frobSq (Δ·S) ≥ ((Δ·S) 0 0)²`.
The polynomial is kept index-natural over `(Fin m × Fin m) ⊕ (Fin m × Fin 4)` (the `Δ`-cube ⊕ `S`-cube),
transported to `Fin n` by the fintype index equiv (`MvPolynomial.renameEquiv` + `piCongrLeft`), so the
coordinate readback stays `rfl`-clean (no `Fin n` index arithmetic). Generic analog of
`RouteMSchurCorank3.frobSqR2c3_ne_zero_ae` / `frobSqShiftR2c3_ne_zero_ae`. -/

/-- The matrix-to-product-index uncurry `(Fin a → Fin b → ℝ) ≃ᵐ ((Fin a × Fin b) → ℝ)`
(`piCurry.symm` to the `Σ`-index, then the `Σ ≃ ×` reindex). MP for volume. -/
noncomputable def matToProdG (a b : ℕ) : (Fin a → Fin b → ℝ) ≃ᵐ ((Fin a × Fin b) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin a) (_ : Fin b) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin a × Fin b => ℝ)
      (Equiv.sigmaEquivProd (Fin a) (Fin b)))

theorem matToProdG_apply (a b : ℕ) (M : Fin a → Fin b → ℝ) (i : Fin a) (j : Fin b) :
    matToProdG a b M (i, j) = M i j := by
  show MeasurableEquiv.piCongrLeft (fun _ : Fin a × Fin b => ℝ)
      (Equiv.sigmaEquivProd (Fin a) (Fin b))
      ((MeasurableEquiv.piCurry (fun (_ : Fin a) (_ : Fin b) => ℝ)).symm M) (i, j) = M i j
  rw [← Equiv.apply_symm_apply (Equiv.sigmaEquivProd (Fin a) (Fin b)) (i, j),
    MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

theorem measurePreserving_matToProdG (a b : ℕ) :
    MeasurePreserving (matToProdG a b) (volume : Measure (Fin a → Fin b → ℝ))
      (volume : Measure ((Fin a × Fin b) → ℝ)) :=
  ((measurePreserving_piCurry (fun (_ : Fin a) (_ : Fin b) => ℝ) (fun _ _ => volume)).symm
      (MeasurableEquiv.piCurry (fun (_ : Fin a) (_ : Fin b) => ℝ))).trans
    (volume_measurePreserving_piCongrLeft (fun _ : Fin a × Fin b => ℝ)
      (Equiv.sigmaEquivProd (Fin a) (Fin b)))

/-- The joint coords `(Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) ≃ᵐ ((Fin m × Fin m) ⊕ (Fin m × Fin 4) → ℝ)`
(uncurry both matrices to product indices, then `sumPiEquivProdPi`). -/
noncomputable def coreJoinG (m : ℕ) :
    ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ))
      ≃ᵐ (((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ) :=
  ((matToProdG m m).prodCongr (matToProdG m 4)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin 4) => ℝ)).symm

theorem coreJoinG_inl (m : ℕ) (q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)) (i j : Fin m) :
    coreJoinG m q (Sum.inl (i, j)) = q.1 i j := by
  show (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin 4) => ℝ)).symm
      (matToProdG m m q.1, matToProdG m 4 q.2) (Sum.inl (i, j)) = q.1 i j
  rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  show matToProdG m m q.1 (i, j) = q.1 i j
  rw [matToProdG_apply]

theorem coreJoinG_inr (m : ℕ) (q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)) (k : Fin m) (j : Fin 4) :
    coreJoinG m q (Sum.inr (k, j)) = q.2 k j := by
  show (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin 4) => ℝ)).symm
      (matToProdG m m q.1, matToProdG m 4 q.2) (Sum.inr (k, j)) = q.2 k j
  rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  show matToProdG m 4 q.2 (k, j) = q.2 k j
  rw [matToProdG_apply]

theorem measurePreserving_coreJoinG (m : ℕ) :
    MeasurePreserving (coreJoinG m)
      (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)))
      (volume : Measure (((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ)) := by
  unfold coreJoinG
  refine MeasurePreserving.trans ?_
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin 4) => ℝ))
  rw [show (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ))) = volume.prod volume
    from rfl,
    show (volume : Measure (((Fin m × Fin m) → ℝ) × ((Fin m × Fin 4) → ℝ))) = volume.prod volume
    from rfl]
  exact (measurePreserving_matToProdG m m).prod (measurePreserving_matToProdG m 4)

open MvPolynomial in
/-- The `(0,0)`-entry polynomial of `Δ·S` over the joint index `(Fin m × Fin m) ⊕ (Fin m × Fin 4)`:
`∑ₖ X(inl(⟨0⟩,k))·X(inr(k,⟨0⟩))` — equals `(Δ·S) 0 0 = ∑ₖ Δ(0,k)·S(k,0)` after eval at `coreJoinG`. -/
noncomputable def coreEntryPolyG (m : ℕ) (hm : 0 < m) :
    MvPolynomial ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) ℝ :=
  ∑ k : Fin m,
    X (Sum.inl (⟨0, hm⟩, k)) * X (Sum.inr (k, ⟨0, by omega⟩))

open MvPolynomial in
/-- **A nonzero MvPolynomial over a FINITE index type is a.e.-nonzero** (the `Fin n`-`ae_eval_ne_zero`
transported through `Fintype.equivFin` via `rename` + the MP coordinate-reindex `arrowCongr'`). Reusable. -/
theorem ae_eval_ne_zero_fintype {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : ι → ℝ, MvPolynomial.eval x p ≠ 0 := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  -- transported polynomial over Fin n
  set q : MvPolynomial (Fin (Fintype.card ι)) ℝ := MvPolynomial.rename e p with hq
  have hqne : q ≠ 0 := by
    rw [hq]; intro h0; exact hp ((MvPolynomial.rename_injective _ e.injective)
      (by rw [h0, MvPolynomial.rename_zero]))
  have hae : ∀ᵐ y : Fin (Fintype.card ι) → ℝ, MvPolynomial.eval y q ≠ 0 :=
    MvPolynomial.ae_eval_ne_zero q hqne
  -- pull back along the MP coordinate-reindex E x = x ∘ e.symm : (ι → ℝ) ≃ᵐ (Fin n → ℝ)
  set E : (ι → ℝ) ≃ᵐ (Fin (Fintype.card ι) → ℝ) :=
    MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ) with hE
  have hmp : MeasurePreserving E volume volume := by
    rw [hE]; exact volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  have hms : MeasurableSet {y : Fin (Fintype.card ι) → ℝ | MvPolynomial.eval y q ≠ 0} :=
    (MvPolynomial.measurableSet_zeroSet q).compl.congr (by ext y; simp)
  have hpull : ∀ᵐ x : ι → ℝ, MvPolynomial.eval (E x) q ≠ 0 := by
    rw [← hmp.map_eq] at hae
    exact (ae_map_iff hmp.measurable.aemeasurable hms).1 hae
  refine hpull.mono (fun x hx => ?_)
  -- eval (E x) q = eval ((x ∘ e.symm) ∘ e) p = eval x p
  rw [hq, MvPolynomial.eval_rename] at hx
  have hcomp : (E x) ∘ e = x := by
    funext i
    show E x (e i) = x i
    rw [hE]
    show x (e.symm (e i)) = x i
    rw [Equiv.symm_apply_apply]
  rw [hcomp] at hx; exact hx

open MvPolynomial in
/-- `eval (coreJoinG m q) (coreEntryPolyG m hm) = ∑ₖ q.1 ⟨0⟩ k · q.2 k ⟨0⟩` (= `(rmatMul q.1 q.2) ⟨0⟩ ⟨0⟩`). -/
theorem eval_coreEntryPolyG (m : ℕ) (hm : 0 < m)
    (q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)) :
    MvPolynomial.eval (coreJoinG m q) (coreEntryPolyG m hm)
      = ∑ k : Fin m, q.1 ⟨0, hm⟩ k * q.2 k ⟨0, by omega⟩ := by
  rw [coreEntryPolyG, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, coreJoinG_inl, coreJoinG_inr]

open MvPolynomial in
/-- `coreEntryPolyG m hm ≠ 0` (witness `Δ ⟨0⟩ ⟨0⟩ = 1`, `S ⟨0⟩ ⟨0⟩ = 1`, rest `0`: eval `= 1`). -/
theorem coreEntryPolyG_ne_zero (m : ℕ) (hm : 0 < m) : coreEntryPolyG m hm ≠ 0 := by
  intro h0
  set Δ0 : Fin m → Fin m → ℝ := fun i k => if i = ⟨0, hm⟩ ∧ k = ⟨0, hm⟩ then 1 else 0 with hΔ0
  set S0 : Fin m → Fin 4 → ℝ := fun k j => if k = ⟨0, hm⟩ ∧ j = ⟨0, by omega⟩ then 1 else 0 with hS0
  have hval : MvPolynomial.eval (coreJoinG m (Δ0, S0)) (coreEntryPolyG m hm) = 1 := by
    rw [eval_coreEntryPolyG]
    rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · rw [hΔ0, hS0]; simp
    · intro k _ hk; rw [hΔ0]; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h0] at hval; simp at hval

/-- **The free core is positive a.e.** `∀ᵐ (Δ,S), 0 < frobSq (rmatMul Δ S)` over the free `m×m` × `m×4`
box (`m > 0`): `frobSq ≥ ((Δ·S) ⟨0⟩ ⟨0⟩)²`, and `(Δ·S) ⟨0⟩ ⟨0⟩ = eval (coreJoinG) (coreEntryPolyG) ≠ 0`
a.e. (`ae_eval_ne_zero_fintype` + the MP `coreJoinG`). Generic analog of `frobSqR2c3_ne_zero_ae`. -/
theorem frobSqG_ne_zero_ae (m : ℕ) (hm : 0 < m) :
    ∀ᵐ q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) ∂(volume),
      0 < frobSq (rmatMul q.1 q.2) := by
  have hae : ∀ᵐ x : ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ,
      MvPolynomial.eval x (coreEntryPolyG m hm) ≠ 0 :=
    ae_eval_ne_zero_fintype (coreEntryPolyG m hm) (coreEntryPolyG_ne_zero m hm)
  have hms : MeasurableSet
      {x : ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ | MvPolynomial.eval x (coreEntryPolyG m hm) ≠ 0} := by
    have : MeasurableSet {x : ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ |
        MvPolynomial.eval x (coreEntryPolyG m hm) = 0} :=
      (MvPolynomial.continuous_eval (coreEntryPolyG m hm)).measurable (measurableSet_singleton 0)
    exact this.compl.congr (by ext x; simp)
  have hpull : ∀ᵐ q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) ∂(volume),
      MvPolynomial.eval (coreJoinG m q) (coreEntryPolyG m hm) ≠ 0 := by
    rw [← (measurePreserving_coreJoinG m).map_eq] at hae
    exact (ae_map_iff (measurePreserving_coreJoinG m).measurable.aemeasurable hms).1 hae
  refine hpull.mono (fun q hq => ?_)
  rw [eval_coreEntryPolyG] at hq
  -- frobSq ≥ ((Δ·S) ⟨0⟩ ⟨0⟩)² > 0
  have hentry : (rmatMul q.1 q.2) ⟨0, hm⟩ ⟨0, by omega⟩ = ∑ k, q.1 ⟨0, hm⟩ k * q.2 k ⟨0, by omega⟩ :=
    rfl
  have hne : (rmatMul q.1 q.2) ⟨0, hm⟩ ⟨0, by omega⟩ ≠ 0 := by rw [hentry]; exact hq
  have hpos : 0 < ((rmatMul q.1 q.2) ⟨0, hm⟩ ⟨0, by omega⟩) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  refine lt_of_lt_of_le hpos ?_
  -- frobSq = ∑ᵢⱼ (Δ·S)ᵢⱼ² ≥ the single (⟨0⟩,⟨0⟩) term
  unfold frobSq
  calc ((rmatMul q.1 q.2) ⟨0, hm⟩ ⟨0, by omega⟩) ^ 2
      = ∑ j ∈ {(⟨0, by omega⟩ : Fin 4)}, ((rmatMul q.1 q.2) ⟨0, hm⟩ j) ^ 2 := by simp
    _ ≤ ∑ j, ((rmatMul q.1 q.2) ⟨0, hm⟩ j) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ i, ∑ j, ((rmatMul q.1 q.2) i j) ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ((rmatMul q.1 q.2) i j) ^ 2)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ _)

/-- **The shifted free core is positive a.e.** `∀ᵐ (Δ,S), 0 < frobSq ((Δ − Sh)·S)` for any fixed `Sh`
(`m > 0`): the translation `(Δ,S) ↦ (Δ + Sh, S)` (MP) reduces it to the unshifted `frobSqG_ne_zero_ae`.
Generic analog of `frobSqShiftR2c3_ne_zero_ae`. -/
theorem frobSqShiftG_ne_zero_ae (m : ℕ) (hm : 0 < m) (Sh : Fin m → Fin m → ℝ) :
    ∀ᵐ q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) ∂(volume),
      0 < frobSq (rmatMul (fun i j => q.1 i j - Sh i j) q.2) := by
  set τ : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) → (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) :=
    fun q => (q.1 + (fun i j => -Sh i j), q.2) with hτ
  have hmpΔ : MeasurePreserving (fun Δ : Fin m → Fin m → ℝ => Δ + (fun i j => -Sh i j))
      volume volume :=
    measurePreserving_add_right volume (fun i j => -Sh i j)
  have hmp : MeasurePreserving τ volume volume := by
    rw [show (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ))) = volume.prod volume
      from rfl]
    exact hmpΔ.prod (MeasurePreserving.id volume)
  have hmsSet : MeasurableSet {q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) |
      0 < frobSq (rmatMul q.1 q.2)} :=
    measurableSet_lt measurable_const (by unfold frobSq rmatMul; fun_prop)
  have hae : ∀ᵐ x ∂(volume.map τ), 0 < frobSq (rmatMul x.1 x.2) := by
    rw [hmp.map_eq]; exact frobSqG_ne_zero_ae m hm
  have hpull : ∀ᵐ q ∂(volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ))),
      0 < frobSq (rmatMul (τ q).1 (τ q).2) :=
    (ae_map_iff hmp.measurable.aemeasurable hmsSet).1 hae
  refine hpull.mono (fun q hq => ?_)
  have hΔeq : (τ q).1 = (fun i j => q.1 i j - Sh i j) := by
    funext i j; show (q.1 + (fun i j => -Sh i j)) i j = q.1 i j - Sh i j
    simp [Pi.add_apply, sub_eq_add_neg]
  have hSeq : (τ q).2 = q.2 := rfl
  rw [hΔeq, hSeq] at hq
  exact hq

/-! ### The carving core — the residual translate-domination into the abstract lower IH

After N2b (`j = 1`) + the shifted `Fin 4` Morse peel, the corank-`r` ratio-residual reduces to the
corank-`(r−1)` JOINT core `∫_{Δ free}∫_{S} frobSq ((Δ − Sh)·S)^{−c''}` at the SHIFTED exponent `c'' =
c' − 2`, with `Δ` the free `(r−1)×(r−1)` block (the `M22` carved from the ratios) and `Sh` the fixed
Cramer shift (`|Sh| ≤ B`). The `Δ ↦ Δ − Sh` matrix-space translation (Jac ≡ 1) box-enlarges `Δ` to radius
`K + B`, and the ABSTRACT lower IH `SchurLowerIH 4 schurLambda r` at corank `r − 1`, radius `K + B`, closes
it (`c'' < λ_{r−1}`). The generic analog of `RouteMSchurCorank3.schurResid2_translate_le`, invoking the IH
instead of the banked `core_schur2_lt_top`. -/

/-- **Matrix-box translate-enlarge (generic `(r−1)×(r−1)`).** `∫_{Δ∈matBox m m K} f(Δ + Sh) ≤
∫_{Δ'∈matBox m m Kg} f Δ'` when `(·+Sh)''(matBox m m K) ⊆ matBox m m Kg`. Measure-preserving matrix-space
translation (`measurePreserving_add_right`) + `lintegral_mono_set`. Mirror of `matBox2_translate_le`. -/
theorem matBoxSq_translate_le {m : ℕ} (Sh : Fin m → Fin m → ℝ) (K Kg : ℝ)
    (f : (Fin m → Fin m → ℝ) → ℝ≥0∞)
    (hsub : (fun Δ => Δ + Sh) '' (matBox m m K) ⊆ matBox m m Kg) :
    (∫⁻ Δ in matBox m m K, f (Δ + Sh)) ≤ ∫⁻ Δ' in matBox m m Kg, f Δ' := by
  set τ : (Fin m → Fin m → ℝ) → (Fin m → Fin m → ℝ) := fun Δ => Δ + Sh with hτ
  have hmp : MeasurePreserving τ volume volume := measurePreserving_add_right volume Sh
  have hemb : MeasurableEmbedding τ := (Homeomorph.addRight Sh).measurableEmbedding
  have h1 : (∫⁻ Δ in matBox m m K, f (τ Δ)) = ∫⁻ Δ' in τ '' (matBox m m K), f Δ' := by
    rw [← hmp.setLIntegral_comp_preimage_emb hemb f (τ '' (matBox m m K)),
      Set.preimage_image_eq (matBox m m K) hemb.injective]
  calc (∫⁻ Δ in matBox m m K, f (Δ + Sh)) = ∫⁻ Δ' in τ '' (matBox m m K), f Δ' := h1
    _ ≤ ∫⁻ Δ' in matBox m m Kg, f Δ' := lintegral_mono_set hsub

/-- **The carving-core residual bound (invokes the abstract IH).** For a fixed shift
`Sh : Fin (r−1) → Fin (r−1) → ℝ` with `|Sh| ≤ B`, `0 < c'' < schurLambda (r−1)`, `K > 0`, `r ≥ 3`,
the shifted corank-`(r−1)` core integral
`∫_{Δ∈matBox (r−1)(r−1) K}∫_{S∈matBox (r−1) 4 K} frobSq ((Δ − Sh)·S)^{−c''}` is finite: the `Δ ↦ Δ − Sh`
translation box-enlarges `Δ` to radius `K + B` (`matBoxSq_translate_le`), and the lower IH at corank
`r − 1`, radius `K + B`, closes it (`SchurCore 4 (r−1) c'' (K+B) < ⊤`). The generic analog of
`schurResid2_translate_lt_top`. -/
theorem schurResidG_translate_lt_top (r : ℕ) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r)
    (Sh : Fin (r - 1) → Fin (r - 1) → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (c'' : ℝ) (hc0 : 0 < c'') (hclam : c'' < schurLambda (r - 1)) (K : ℝ) (hK : 0 < K) :
    (∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) 4 K,
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c''))) < ⊤ := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB ⟨0, by omega⟩ ⟨0, by omega⟩)
  -- the lower IH at corank r−1, radius K+B (j = 1, so r − j = r − 1)
  have hcore : SchurCore 4 (r - 1) c'' (K + B) := by
    have hj1 : (1 : ℕ) ≤ 1 := le_refl 1
    have hjr : (1 : ℕ) ≤ r := by omega
    have := hIH 1 hj1 hjr c'' hc0 (by simpa using hclam) (K + B) (by linarith)
    simpa using this
  rw [SchurCore] at hcore
  set g : (Fin (r - 1) → Fin (r - 1) → ℝ) → ℝ≥0∞ := fun Δ =>
    ∫⁻ S in matBox (r - 1) 4 (K + B),
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) with hg
  have hSsub : matBox (r - 1) 4 K ⊆ matBox (r - 1) 4 (K + B) := by
    intro X hX i k; have := Set.mem_Icc.1 (hX i k); rw [Set.mem_Icc]
    constructor <;> [linarith [this.1]; linarith [this.2]]
  have hle1 : ∀ Δ : Fin (r - 1) → Fin (r - 1) → ℝ,
      (∫⁻ S in matBox (r - 1) 4 K,
          ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
        ≤ g (Δ + (fun i j => -Sh i j)) := by
    intro Δ
    have hmono := lintegral_mono_set (μ := volume) hSsub
      (f := fun S => ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
    refine le_trans hmono (le_of_eq ?_)
    have heqfun : (fun i j => Δ i j - Sh i j) = (Δ + (fun i j => -Sh i j)) := by
      funext i j; simp [Pi.add_apply, sub_eq_add_neg]
    rw [hg]
    refine lintegral_congr (fun S => ?_)
    rw [heqfun]
  refine lt_of_le_of_lt (lintegral_mono hle1) ?_
  have hsub : (fun Δ => Δ + (fun i j => -Sh i j)) '' (matBox (r - 1) (r - 1) K)
      ⊆ matBox (r - 1) (r - 1) (K + B) := by
    rintro Δ' ⟨Δ, hΔ, rfl⟩
    intro i j
    show -(K + B) ≤ Δ i j + (-Sh i j) ∧ Δ i j + (-Sh i j) ≤ K + B
    have hΔij := Set.mem_Icc.1 (hΔ i j)
    have hShij := abs_le.1 (hB i j)
    constructor <;> [linarith [hΔij.1, hShij.2]; linarith [hΔij.2, hShij.1]]
  refine lt_of_le_of_lt (matBoxSq_translate_le (fun i j => -Sh i j) K (K + B) g hsub) ?_
  exact hcore

/-! ### The Sh-UNIFORM `_le` residual (for integration over the boundary `(g,b)` box)

`schurResidG_translate_lt_top` is only `< ⊤` — pointwise finiteness in the shift `Sh` does not integrate
over the `(g,b)` boundary box. The carving integrates the residual over `Sh = bgShiftG(g,b)` (a finite
box), so it needs a bound INDEPENDENT of `Sh`: bound the shifted residual by the named constant
`coreSchurGenVal (r−1) c'' (K+B)` (the unshifted free corank-`(r−1)` core at the enlarged radius `K+B`,
finite by the abstract IH). Generic analog of `RouteMSchurCorank3.coreSchur2Val` / `schurResid2_translate_le`. -/

/-- **The unshifted free corank-`m` core value** `coreSchurGenVal m c'' Kr := ∫_{Δ∈matBox m m Kr}
∫_{S∈matBox m 4 Kr} frobSq(Δ·S)^{−c''}` — the `Sh`-independent constant the shifted residual is bounded by. -/
noncomputable def coreSchurGenVal (m : ℕ) (c'' Kr : ℝ) : ℝ≥0∞ :=
  ∫⁻ Δ in matBox m m Kr, ∫⁻ S in matBox m 4 Kr,
    ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))

/-- `coreSchurGenVal (r−1) c'' Kr < ⊤` for `0 < c'' < schurLambda (r−1)`, `0 < Kr`, `r ≥ 3` — exactly
`SchurCore 4 (r−1) c'' Kr` from the abstract IH (at `j = 1`). -/
theorem coreSchurGenVal_lt_top (r : ℕ) (hr : 3 ≤ r) (hIH : SchurLowerIH 4 schurLambda r)
    (c'' : ℝ) (hc0 : 0 < c'') (hclam : c'' < schurLambda (r - 1)) (Kr : ℝ) (hKr : 0 < Kr) :
    coreSchurGenVal (r - 1) c'' Kr < ⊤ := by
  have hcore : SchurCore 4 (r - 1) c'' Kr :=
    hIH 1 (le_refl 1) (by omega) c'' hc0 (by simpa using hclam) Kr hKr
  rwa [SchurCore] at hcore

/-- **The Sh-uniform `_le` residual bound.** For a fixed shift `Sh : Fin (r−1) → Fin (r−1) → ℝ` with
`|Sh| ≤ B`, the shifted corank-`(r−1)` core integral is `≤ coreSchurGenVal (r−1) c'' (K+B)` — a bound
INDEPENDENT of `Sh` (only the radius `K+B` records the shift's size). Same chain as
`schurResidG_translate_lt_top` (S-monotone enlarge `K → K+B`, then translate `Δ ↦ Δ − Sh` into radius
`K+B`), ending at the named value rather than `< ⊤`. Generic analog of `schurResid2_translate_le`. -/
theorem schurResidG_translate_le (r : ℕ) (hr : 3 ≤ r)
    (Sh : Fin (r - 1) → Fin (r - 1) → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (c'' : ℝ) (K : ℝ) :
    (∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) 4 K,
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
      ≤ coreSchurGenVal (r - 1) c'' (K + B) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB ⟨0, by omega⟩ ⟨0, by omega⟩)
  set g : (Fin (r - 1) → Fin (r - 1) → ℝ) → ℝ≥0∞ := fun Δ =>
    ∫⁻ S in matBox (r - 1) 4 (K + B),
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) with hg
  have hSsub : matBox (r - 1) 4 K ⊆ matBox (r - 1) 4 (K + B) := by
    intro X hX i k; have := Set.mem_Icc.1 (hX i k); rw [Set.mem_Icc]
    constructor <;> [linarith [this.1]; linarith [this.2]]
  have hle1 : ∀ Δ : Fin (r - 1) → Fin (r - 1) → ℝ,
      (∫⁻ S in matBox (r - 1) 4 K,
          ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
        ≤ g (Δ + (fun i j => -Sh i j)) := by
    intro Δ
    have hmono := lintegral_mono_set (μ := volume) hSsub
      (f := fun S => ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
    refine le_trans hmono (le_of_eq ?_)
    have heqfun : (fun i j => Δ i j - Sh i j) = (Δ + (fun i j => -Sh i j)) := by
      funext i j; simp [Pi.add_apply, sub_eq_add_neg]
    rw [hg]; refine lintegral_congr (fun S => ?_); rw [heqfun]
  refine le_trans (lintegral_mono hle1) ?_
  have hsub : (fun Δ => Δ + (fun i j => -Sh i j)) '' (matBox (r - 1) (r - 1) K)
      ⊆ matBox (r - 1) (r - 1) (K + B) := by
    rintro Δ' ⟨Δ, hΔ, rfl⟩
    intro i j
    show -(K + B) ≤ Δ i j + (-Sh i j) ∧ Δ i j + (-Sh i j) ≤ K + B
    have hΔij := Set.mem_Icc.1 (hΔ i j)
    have hShij := abs_le.1 (hB i j)
    constructor <;> [linarith [hΔij.1, hShij.2]; linarith [hΔij.2, hShij.1]]
  refine le_trans (matBoxSq_translate_le (fun i j => -Sh i j) K (K + B) g hsub) (le_of_eq ?_)
  rw [coreSchurGenVal]

/-! ### The a.e. Tonelli `T`-peel (the shifted Morse-block peel, local copy of `core_T_peel_le_ae_c3`) -/

/-- **The a.e. Tonelli `T`-peel bound** (local copy of `RouteMSchurCorank3.core_T_peel_le_ae_c3`, built
on the imported `radial_morse_residual_power_le`). With `w > 0` only a.e. on `Z`, the joint Morse-block
peel `∫_z ∫_T (∑Tᵢ² + w z)^{−c'} ≤ Cresid·∫_z (w z)^{−(c'−(m+1)/2)}`. -/
theorem core_T_peel_le_aeG {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : (m + 1 : ℝ) / 2 < c')
    (Tw : ℝ) (hTw : 0 < Tw) (w : Ω → ℝ) (Z : Set Ω)
    (hwpos : ∀ᵐ z ∂(μ.restrict Z), 0 < w z) :
    (∫⁻ z in Z, (∫⁻ T in morseBox (m + 1) Tw,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))) ∂μ)
      ≤ ENNReal.ofReal (Cresid (m + 1) c')
        * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
  calc (∫⁻ z in Z, (∫⁻ T in morseBox (m + 1) Tw,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))) ∂μ)
      ≤ ∫⁻ z in Z, ENNReal.ofReal (Cresid (m + 1) c')
          * ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
        refine lintegral_mono_ae (hwpos.mono (fun z hz => ?_))
        rw [← ENNReal.ofReal_mul (Cresid_nonneg _ _)]
        exact radial_morse_residual_power_le m c' hc' Tw hTw (w z) hz
    _ = ENNReal.ofReal (Cresid (m + 1) c')
          * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
        rw [lintegral_const_mul']; exact ENNReal.ofReal_ne_top

/-! ### The SHIFTED resolved-form (the JOINT brick: a.e. peel + uniform shifted residual)

The corank-`r` inner-`S`, after the N2b `j=1` split and the top-row shear, is the SHIFTED resolved form:
a `Fin 4` Morse spectator `T` disjoint-summed onto the SHIFTED corank-`(r−1)` core
`frobSq ((Δ − Sh)·S)` (`Δ = M22` the free angular block, `Sh = g·bᵀ` the boundary-ratio rank-1 shift,
`S = S_bot`). The a.e. peel (`core_T_peel_le_aeG`, threshold `4/2 = 2 < c'`) leaves the shifted residual
at exponent `c'' = c'−2 < λ_{r−1}`, bounded UNIFORMLY in `Sh` by `coreSchurGenVal (r−1) (c'−2) (K+B)`
(`schurResidG_translate_le`). Generic analog of `RouteMSchurCorank3.resolvedShiftR2c3_le`. -/

/-- **The SHIFTED resolved-form UNIFORM `_le` bound (the JOINT brick).** For a fixed shift
`Sh : Fin (r−1) → Fin (r−1) → ℝ` with `|Sh i j| ≤ B`, `2 < c'`, every `K > 0`,
`∫_{Δ∈matBox (r−1)(r−1) K}∫_{S∈matBox (r−1) 4 K}∫_{T∈morseBox 4 K}(∑T² + frobSq((Δ−Sh)·S))^{−c'}` is
bounded by `ofReal(Cresid 4 c') · coreSchurGenVal (r−1) (c'−2) (K+B)` — INDEPENDENT of `Sh`. The `T`-peel
(`core_T_peel_le_aeG`, `m=3`, threshold `2`) on the shifted core (`> 0` a.e. by `frobSqShiftG_ne_zero_ae`)
leaves the residual at `c'−2`, closed by `schurResidG_translate_le`. Generic analog of `resolvedShiftR2c3_le`. -/
theorem resolvedShiftRG_le (r : ℕ) (hr : 3 ≤ r)
    (Sh : Fin (r - 1) → Fin (r - 1) → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (K : ℝ) (hK : 0 < K) (c' : ℝ) (hc2 : 2 < c') :
    (∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) 4 K, ∫⁻ T in morseBox 4 K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2
          + frobSq (rmatMul (fun a b => Δ a b - Sh a b) S)) ^ (-c')))
      ≤ ENNReal.ofReal (Cresid 4 c') * coreSchurGenVal (r - 1) (c' - 2) (K + B) := by
  have hm : 0 < r - 1 := by omega
  set w : (Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin 4 → ℝ) → ℝ :=
    fun q => frobSq (rmatMul (fun a b => q.1 a b - Sh a b) q.2) with hwdef
  have hmeasT : Measurable (fun q : ((Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin 4 → ℝ))
      × (Fin 4 → ℝ) => ENNReal.ofReal ((∑ i, (q.2 i) ^ 2 + w q.1) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    show Measurable (fun q : ((Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin 4 → ℝ))
        × (Fin 4 → ℝ) =>
        (∑ i, (q.2 i) ^ 2 + frobSq (rmatMul (fun a b => q.1.1 a b - Sh a b) q.1.2)))
    unfold frobSq rmatMul; fun_prop
  -- Step 1: Tonelli ∫_Δ∫_S∫_T = ∫_{(Δ,S)}∫_T over the product box
  have hstep1 : ∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) 4 K, ∫⁻ T in morseBox 4 K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul (fun a b => Δ a b - Sh a b) S)) ^ (-c'))
      = ∫⁻ q in (matBox (r - 1) (r - 1) K ×ˢ matBox (r - 1) 4 K), (∫⁻ T in morseBox 4 K,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w q) ^ (-c'))) ∂volume := by
    rw [Measure.volume_eq_prod (Fin (r - 1) → Fin (r - 1) → ℝ) (Fin (r - 1) → Fin 4 → ℝ),
      setLIntegral_prod _ (Measurable.lintegral_prod_right hmeasT).aemeasurable]
  rw [hstep1]
  -- Step 2: the a.e. T-peel (m = 3): bound by Cresid · ∫_{(Δ,S)} w^{−(c'−2)}
  have hwpos : ∀ᵐ z ∂(volume.restrict (matBox (r - 1) (r - 1) K ×ˢ matBox (r - 1) 4 K)), 0 < w z :=
    ae_restrict_of_ae (frobSqShiftG_ne_zero_ae (r - 1) hm Sh)
  have hpeel := core_T_peel_le_aeG (m := 3) (volume) c' (by norm_num; linarith) K hK w
    (matBox (r - 1) (r - 1) K ×ˢ matBox (r - 1) 4 K) hwpos
  refine le_trans hpeel ?_
  -- Step 3: the residual ∫_{(Δ,S)} w^{−(c'−2)} = ∫_Δ∫_S frobSq((Δ−Sh)·S)^{−(c'−2)} ≤ schurResidG_translate_le
  refine mul_le_mul_left' ?_ _
  have hmeasResid : Measurable
      (fun q : (Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin 4 → ℝ) =>
        ENNReal.ofReal ((w q) ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2))) (by fun_prop)
    show Measurable (fun q : (Fin (r - 1) → Fin (r - 1) → ℝ) × (Fin (r - 1) → Fin 4 → ℝ) =>
        frobSq (rmatMul (fun a b => q.1 a b - Sh a b) q.2))
    unfold frobSq rmatMul; fun_prop
  have hresid : (∫⁻ q in (matBox (r - 1) (r - 1) K ×ˢ matBox (r - 1) 4 K),
        ENNReal.ofReal ((w q) ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2))))
      = ∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) 4 K,
          ENNReal.ofReal ((frobSq (rmatMul (fun a b => Δ a b - Sh a b) S)) ^ (-(c' - 2))) := by
    rw [Measure.volume_eq_prod (Fin (r - 1) → Fin (r - 1) → ℝ) (Fin (r - 1) → Fin 4 → ℝ),
      setLIntegral_prod _ hmeasResid.aemeasurable]
    refine setLIntegral_congr_fun (matBox_measurableSet (r - 1) (r - 1) K) (fun Δ _ => ?_)
    refine setLIntegral_congr_fun (matBox_measurableSet (r - 1) 4 K) (fun S _ => ?_)
    rw [hwdef]; norm_num
  rw [hresid]
  exact schurResidG_translate_le r hr Sh B hB (c' - 2) K

/-! ### Pivot-WLOG: the `(0,0)`-normalised angular matrix (mirror of `Rmat334norm`/`angA1Int_eq_norm`) -/

/-- For `k ≠ p`, the read-back `((piRatioG r N hN p).symm (0,z)) k` is some ratio `z j ∈ [−1,1]`, so
`|·| ≤ 1` on the box `[−1,1]^N`. (The pivot-axis-`0` read-back is `≤ 1` off the pivot; mirror of the
chart-domain pullback in `schur_matBoxG_chart_lt_top`.) -/
theorem piRatioG_symm_offpivot_le (r N : ℕ) (hN : r * r = N + 1) (p : Fin (r * r))
    (z : Fin N → ℝ) (hz : z ∈ Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))
    (k : Fin (r * r)) (hk : k ≠ p) :
    |((piRatioG r N hN p).symm (0, z)) k| ≤ 1 := by
  have hne : finCongr hN k ≠ finCongr hN p := fun h => hk ((finCongr hN).injective h)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
  have hk_eq : k = (finCongr hN).symm ((finCongr hN p).succAbove j) := by
    rw [hj]; exact ((finCongr hN).symm_apply_apply k).symm
  -- ((piRatioG …).symm (0,z)) k = (piRatioG …) forward inverse; off-pivot it reads z j
  have hval : ((piRatioG r N hN p).symm (0, z)) k = z j := by
    rw [piRatioG_symm_apply, hk_eq]
    -- finCongr hN k = (finCongr hN p).succAbove j, so insertNth reads z at j
    have : finCongr hN ((finCongr hN).symm ((finCongr hN p).succAbove j))
        = (finCongr hN p).succAbove j := (finCongr hN).apply_symm_apply _
    rw [this]
    simp [Fin.insertNthEquiv, Fin.insertNth_apply_succAbove]
  rw [hval]
  have := hz j (Set.mem_univ j); rw [Set.mem_Icc, ← abs_le] at this; exact this

/-- The pivot-normalised angular matrix on chart `p`, ratios `z : Fin N → ℝ` (`r*r = N+1`):
`R' a b = RmatG r p (…symm(0,z)) (σr a) (σc b)` with `σr = swap r₀ 0`, `σc = swap c₀ 0`,
`(r₀,c₀) = (eG r).symm p`. Pivot `1` at `(0,0)`. (Threads the shared `hN` so all proof terms unify.) -/
noncomputable def RmatGnorm (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r))
    (z : Fin N → ℝ) : Fin r → Fin r → ℝ :=
  fun a b => RmatG r p ((piRatioG r N hN p).symm (0, z))
    ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) a) ((Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) b)

/-- `RmatGnorm … z ⟨0⟩ ⟨0⟩ = 1`: the `(0,0)` entry is the pivot. -/
theorem RmatGnorm_pivot (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r))
    (z : Fin N → ℝ) :
    RmatGnorm r N hN hr p z ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
  unfold RmatGnorm
  rw [Equiv.swap_apply_right, Equiv.swap_apply_right, RmatG_entry, if_pos]
  rw [show (((eG r).symm p).1, ((eG r).symm p).2) = (eG r).symm p from rfl, Equiv.apply_symm_apply]

/-- The matrix index of `(σr a, σc b)` is the pivot `p` iff `(a,b) = (0,0)`; off `(0,0)` it is `≠ p`. -/
theorem RmatGnorm_offpivot_idx (r : ℕ) (hr : 3 ≤ r) (p : Fin (r * r)) (a b : Fin r)
    (hab : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩)) :
    eG r ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) a,
        (Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) b) ≠ p := by
  set σr := Equiv.swap ((eG r).symm p).1 (⟨0, by omega⟩ : Fin r) with hσr
  set σc := Equiv.swap ((eG r).symm p).2 (⟨0, by omega⟩ : Fin r) with hσc
  have hσr0 : σr ⟨0, by omega⟩ = ((eG r).symm p).1 := by rw [hσr, Equiv.swap_apply_right]
  have hσc0 : σc ⟨0, by omega⟩ = ((eG r).symm p).2 := by rw [hσc, Equiv.swap_apply_right]
  have hpe : eG r (((eG r).symm p).1, ((eG r).symm p).2) = p := by
    rw [show (((eG r).symm p).1, ((eG r).symm p).2) = (eG r).symm p from rfl, Equiv.apply_symm_apply]
  intro heq
  rw [← hpe] at heq
  obtain ⟨hi, hj⟩ := Prod.mk.injEq .. ▸ (eG r).injective heq
  rw [← hσr0] at hi; rw [← hσc0] at hj
  exact hab ⟨σr.injective hi, σc.injective hj⟩

/-- Off-`(0,0)` entries of `RmatGnorm … z` are `z`-components, hence `|·| ≤ 1` on `[−1,1]^N`. -/
theorem RmatGnorm_offpivot_le (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r))
    (z : Fin N → ℝ) (hz : z ∈ Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))
    (a b : Fin r) (hab : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩)) :
    |RmatGnorm r N hN hr p z a b| ≤ 1 := by
  unfold RmatGnorm
  rw [RmatG_entry, if_neg (RmatGnorm_offpivot_idx r hr p a b hab)]
  exact piRatioG_symm_offpivot_le r N hN p z hz _ (RmatGnorm_offpivot_idx r hr p a b hab)

/-- **`innerSGen` in the pivot-normalised form.** `innerSGen r c' T p (…symm(0,z)) = ∫_{S∈box r 4 T}
frobSq(RmatGnorm·S)^{−c'}`: row/col-permute `RmatG` by `σr,σc` (`frobSq_rmatMul_permG`) under the
`S`-row-permute change of variables (`matBox_rowperm_lintegralG`). Mirror of `angA1Int_eq_norm`. -/
theorem innerSGen_eq_norm (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (c' : ℝ) (T : ℝ)
    (p : Fin (r * r)) (z : Fin N → ℝ) :
    innerSGen r c' T p ((piRatioG r N hN p).symm (0, z))
      = ∫⁻ S in matBox r 4 T,
          ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr p z) S)) ^ (-c')) := by
  set y := (piRatioG r N hN p).symm (0, z) with hy
  set σr := Equiv.swap ((eG r).symm p).1 (⟨0, by omega⟩ : Fin r) with hσr
  set σc := Equiv.swap ((eG r).symm p).2 (⟨0, by omega⟩ : Fin r) with hσc
  rw [innerSGen]
  rw [matBox_rowperm_lintegralG T σc
    (fun S => ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr p z) S)) ^ (-c')))]
  refine lintegral_congr (fun S => ?_)
  congr 2
  exact frobSq_rmatMul_permG (RmatG r p y) S σr σc

/-- The `z`-slot of a matrix cell `(a,b) ≠ (0,0)`: the `Fin N` index whose `piRatioG`-decode is
`eG (σr a, σc b)`. Generic analog of `zslot`; spec is `RmatGnorm_eq_slot`. -/
noncomputable def slotMatG (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r))
    (a b : Fin r) : Fin N :=
  if h : eG r ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) a,
      (Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) b) ≠ p then
    (Fin.exists_succAbove_eq (show
      finCongr hN (eG r ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) a,
        (Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) b))
      ≠ finCongr hN p from fun he => h ((finCongr hN).injective he))).choose
  else ⟨0, by have h9 : 3 * 3 ≤ r * r := Nat.mul_le_mul hr hr; omega⟩

/-- The read-back: `RmatGnorm … z a b = z (slotMatG … a b)` for `(a,b) ≠ (0,0)`. Generic analog of
`Rmat334norm_eq_zslot`. -/
theorem RmatGnorm_eq_slot (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r))
    (z : Fin N → ℝ) (a b : Fin r) (hab : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩)) :
    RmatGnorm r N hN hr p z a b = z (slotMatG r N hN hr p a b) := by
  set σr := Equiv.swap ((eG r).symm p).1 (⟨0, by omega⟩ : Fin r) with hσr
  set σc := Equiv.swap ((eG r).symm p).2 (⟨0, by omega⟩ : Fin r) with hσc
  have hidx : eG r (σr a, σc b) ≠ p := RmatGnorm_offpivot_idx r hr p a b hab
  have hentry : RmatGnorm r N hN hr p z a b = (piRatioG r N hN p).symm (0, z) (eG r (σr a, σc b)) := by
    rw [RmatGnorm, RmatG_entry, if_neg hidx]
  rw [hentry]
  have hne : finCongr hN (eG r (σr a, σc b)) ≠ finCongr hN p :=
    fun he => hidx ((finCongr hN).injective he)
  have hslot : slotMatG r N hN hr p a b = (Fin.exists_succAbove_eq hne).choose := by
    rw [slotMatG, dif_pos hidx]
  have hspec : (finCongr hN p).succAbove (slotMatG r N hN hr p a b)
      = finCongr hN (eG r (σr a, σc b)) := by
    rw [hslot]; exact (Fin.exists_succAbove_eq hne).choose_spec
  rw [piRatioG_symm_apply, ← hspec]
  simp [Fin.insertNthEquiv, Fin.insertNth_apply_succAbove]

/-! ### The N2b lower bound → top-row shear → resolved form (per-`z`; mirror of `angularA1_integral_le` + `step3a`) -/

/-- **Pointwise antitone domination from a two-sided comparison's lower leg.** If `c₀·X ≤ F` with
`0 < c₀`, `0 ≤ X`, `0 ≤ F`, then `F^{−c'} ≤ c₀^{−c'}·X^{−c'}` (`0 < c'`): on `X > 0` (so `F > 0`) the
base-antitone `rpow`; at `X = 0` the LHS `F^{−c'} ≤` … but `F` may be `> 0`, giving `F^{−c'} ≤ ∞ = c₀^{−c'}·0^{−c'}`
since `0^{−c'} = 0` makes the RHS `0` — handled by the `X=0 ⟹ F=0` coincidence: `c₀·0 ≤ F` is vacuous, so
we instead require the zero-coincidence `X = 0 → F = 0`. -/
theorem ofReal_rpow_le_const_mul (X F c₀ c' : ℝ) (hc0 : 0 < c') (hcc : 0 < c₀)
    (hX : 0 ≤ X) (hF : 0 ≤ F) (hle : c₀ * X ≤ F) (hzero : X = 0 → F = 0) :
    ENNReal.ofReal (F ^ (-c')) ≤ ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal (X ^ (-c')) := by
  rcases eq_or_lt_of_le hX with hX0 | hX0
  · -- X = 0 ⟹ F = 0: LHS = 0^{−c'} = 0
    rw [hzero hX0.symm, Real.zero_rpow (by linarith), ENNReal.ofReal_zero]; exact zero_le _
  · -- X > 0 ⟹ c₀·X > 0; F ≥ c₀·X, base-antitone rpow
    have hcX : (0 : ℝ) < c₀ * X := by positivity
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hcc) _),
      ← Real.mul_rpow (le_of_lt hcc) (le_of_lt hX0)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact Real.rpow_le_rpow_of_nonpos hcX hle (by linarith)

/-- **The translation-and-enlargement atom** (local copy of `RouteM334Ratiofin.lintegral_translate_le`):
`∫_{v∈B} f (v + s) ≤ ∫_{w∈BG} f w` when `(·+s)''B ⊆ BG` (`measurePreserving_add_right` + `lintegral_mono_set`). -/
theorem lintegral_translate_leG (n : ℕ) (s : Fin n → ℝ)
    (B BG : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ≥0∞)
    (hsub : (fun v => v + s) '' B ⊆ BG) :
    (∫⁻ v in B, f (v + s)) ≤ ∫⁻ w in BG, f w := by
  set τ : (Fin n → ℝ) → (Fin n → ℝ) := fun v => v + s with hτ
  have hmp : MeasurePreserving τ volume volume := measurePreserving_add_right volume s
  have hemb : MeasurableEmbedding τ := (Homeomorph.addRight s).measurableEmbedding
  have h1 : (∫⁻ v in B, f (τ v)) = ∫⁻ w in τ '' B, f w := by
    rw [← hmp.setLIntegral_comp_preimage_emb hemb f (τ '' B),
      Set.preimage_image_eq B hemb.injective]
  calc (∫⁻ v in B, f (v + s)) = ∫⁻ w in τ '' B, f w := h1
    _ ≤ ∫⁻ w in BG, f w := lintegral_mono_set hsub

/-- **The top-row shear (generic `step3a`).** For couplings `b : Fin m → ℝ` (`|b a| ≤ 1`) and a fixed
`m×m` `Sc`, the `(m+1)×4` `S`-box integral of the top-row-coupled integrand is dominated by the
`(S_bot, T')` resolved form: split `S = S_top × S_bot` (`piFinSuccAbove 0`, MP), then the per-`S_bot`
translation `S_top ↦ T' = S_top + (b·S_bot)` peels the spectator row (`|b·S_bot| ≤ m·T`, box
`[−T,T]^4 → [−(m+1)T,(m+1)T]^4 = morseBox 4 ((m+1)·T)`). Mirror of `RouteM334Ratiofin.step3a`. -/
theorem stepShearG (m : ℕ) (b : Fin m → ℝ) (hb : ∀ a, |b a| ≤ 1)
    (Sc : Matrix (Fin m) (Fin m) ℝ) (T : ℝ) (hT : 0 < T) (c' : ℝ) :
    (∫⁻ S in matBox (m + 1) 4 T,
        ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
          + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')))
      ≤ ∫⁻ S_bot in matBox m 4 T, ∫⁻ T' in morseBox 4 ((m + 1 : ℕ) * T),
          ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin 4 → ℝ) 0 with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => Fin 4 → ℝ) 0
  -- the joint integrand on (S_top, S_bot)
  set H : (Fin 4 → ℝ) × (Fin m → Fin 4 → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((∑ qq, (q.1 qq + ∑ a, b a * q.2 a qq) ^ 2)
      + frobSq (rmatMul Sc q.2)) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ (fun qq _ => ?_)
      refine Measurable.pow_const ?_ 2
      have h0 : Measurable (fun q : (Fin 4 → ℝ) × (Fin m → Fin 4 → ℝ) => q.1 qq) :=
        (measurable_pi_apply qq).comp measurable_fst
      refine h0.add (Finset.measurable_sum _ (fun a _ => ?_))
      exact measurable_const.mul ((measurable_pi_apply qq).comp
        ((measurable_pi_apply a).comp measurable_snd))
    · unfold frobSq rmatMul
      refine Finset.measurable_sum _ (fun i _ => ?_)
      refine Finset.measurable_sum _ (fun j _ => ?_)
      refine Measurable.pow_const ?_ 2
      refine Finset.measurable_sum _ (fun k _ => ?_)
      exact measurable_const.mul ((measurable_pi_apply j).comp
        ((measurable_pi_apply k).comp measurable_snd))
  -- the box split: matBox (m+1) 4 T = e ⁻¹' (matBox 1-row × matBox m 4 T) — as a Fin 4 row box × matBox
  have hsplit : matBox (m + 1) 4 T
      = e ⁻¹' ((Set.univ.pi (fun _ : Fin 4 => Set.Icc (-T) T)) ×ˢ matBox m 4 T) := by
    ext S
    simp only [he, Set.mem_preimage, Set.mem_prod, matBox, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h
      refine ⟨fun q => h 0 q, fun a q => h a.succ q⟩
    · rintro ⟨h1, h2⟩ i k
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · exact h1 k
      · exact h2 i' k
  -- LHS = ∫ over (S_top × S_bot) of H, then Tonelli (S_bot outer)
  have hLHS : (∫⁻ S in matBox (m + 1) 4 T,
      ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
        + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')))
      = ∫⁻ pq in ((Set.univ.pi (fun _ : Fin 4 => Set.Icc (-T) T)) ×ˢ matBox m 4 T), H pq := by
    rw [hsplit, ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding H
        ((Set.univ.pi (fun _ : Fin 4 => Set.Icc (-T) T)) ×ˢ matBox m 4 T)]
    refine setLIntegral_congr_fun ?_ (fun S _ => rfl)
    exact e.measurable (MeasurableSet.prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (matBox_measurableSet m 4 T))
  rw [hLHS, Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable,
    lintegral_lintegral_swap hHmeas.aemeasurable]
  -- now ∫_{S_bot}∫_{S_top} H (S_top, S_bot); shear S_top ↦ T' per fixed S_bot
  refine setLIntegral_mono_ae' (matBox_measurableSet m 4 T) (ae_of_all _ (fun S_bot hSbot => ?_))
  -- per S_bot: translate S_top ↦ T' = S_top + (b·S_bot), box enlarges to morseBox 4 ((m+1)T)
  set shift : Fin 4 → ℝ := fun q => ∑ a, b a * S_bot a q with hshift
  set f : (Fin 4 → ℝ) → ℝ≥0∞ := fun T' =>
    ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) with hf
  have hrw : ∀ S_top : Fin 4 → ℝ, H (S_top, S_bot) = f (S_top + shift) := by
    intro S_top; rw [hHdef, hf]; rfl
  rw [lintegral_congr hrw]
  refine lintegral_translate_leG 4 shift (Set.univ.pi (fun _ : Fin 4 => Set.Icc (-T) T))
    (morseBox 4 ((m + 1 : ℕ) * T)) f ?_
  rintro T' ⟨v, hv, rfl⟩
  simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro q
  have hvq := Set.mem_Icc.1 (hv q)
  -- |shift q| = |∑ a b a · S_bot a q| ≤ m·T ≤ ... ; v q + shift q ∈ [−(m+1)T, (m+1)T]
  have htermbd : ∀ a : Fin m, |b a * S_bot a q| ≤ T := by
    intro a
    rw [abs_mul]
    have hSa := Set.mem_Icc.1 (hSbot a q)
    calc |b a| * |S_bot a q| ≤ 1 * T :=
          mul_le_mul (hb a) (abs_le.2 hSa) (abs_nonneg _) (by norm_num)
      _ = T := by ring
  have hshiftbd : |shift q| ≤ (m : ℝ) * T := by
    rw [hshift]
    calc |∑ a, b a * S_bot a q| ≤ ∑ a, |b a * S_bot a q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin m, T := Finset.sum_le_sum (fun a _ => htermbd a)
      _ = (m : ℝ) * T := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Set.mem_Icc, Pi.add_apply, hshift]
  have habs := abs_le.1 hshiftbd
  push_cast
  constructor <;> [nlinarith [hvq.1, habs.1, hT]; nlinarith [hvq.2, habs.2, hT]]

/-! ### The carve: `z ≅ (M22, g, b)` coordinate permutation + the `Sc = matOf M22 − bgShiftG (g,b)` readback

The `N = r²−1` ratio coords `z` are exactly the off-`(0,0)` cells of the `(0,0)`-normalised angular matrix,
partitioned into the `(r−1)²` lower-right `M22` cells `(a.succ, b.succ)`, the `(r−1)` `g`-cells
`(a.succ, 0)`, and the `(r−1)` `b`-cells `(0, b.succ)` (`(r−1)²+2(r−1)=r²−1=N`). The slot bijection
`zσG` carries this; the reshape `zEG` (`piCongrLeft ∘ sumPiEquivProdPi`, MP) splits `z` into the `M22`-cube
and the `(g,b)`-cube; at `j=1` the Schur complement reads `Sc = matOf M22 − bgShiftG (g,b)`
(`Sh_{ab} = g a · b b`, `|Sh| ≤ 1`). Generic analog of `RouteM334Ratiofin.cellOf`/`zslot`/`zσ`/`zE`/`Δof_eq_zE`. -/

/-- The enumeration of the off-`(0,0)` cells: `inl (a,b) ↦ (a.succ, b.succ)` (M22), `inr (inl a) ↦
(a.succ, 0)` (g), `inr (inr b) ↦ (0, b.succ)` (b). -/
def cellOfG (m : ℕ) : ((Fin m × Fin m) ⊕ (Fin m ⊕ Fin m)) → Fin (m + 1) × Fin (m + 1)
  | Sum.inl (a, b) => (a.succ, b.succ)
  | Sum.inr (Sum.inl a) => (a.succ, 0)
  | Sum.inr (Sum.inr b) => (0, b.succ)

theorem cellOfG_ne_zero (m : ℕ) (s : (Fin m × Fin m) ⊕ (Fin m ⊕ Fin m)) :
    ¬ ((cellOfG m s).1 = 0 ∧ (cellOfG m s).2 = 0) := by
  rcases s with ⟨a, b⟩ | (a | b) <;> simp [cellOfG, Fin.succ_ne_zero]

theorem cellOfG_injective (m : ℕ) : Function.Injective (cellOfG m) := by
  rintro s1 s2 h
  rcases s1 with ⟨a1, b1⟩ | (a1 | b1) <;> rcases s2 with ⟨a2, b2⟩ | (a2 | b2) <;>
    simp only [cellOfG, Prod.mk.injEq] at h <;>
    first
      | (obtain ⟨ha, hb⟩ := h; rw [Fin.succ_inj] at ha hb; subst ha; subst hb; rfl)
      | (obtain ⟨ha, _⟩ := h; rw [Fin.succ_inj] at ha; subst ha; rfl)
      | (obtain ⟨_, hb⟩ := h; rw [Fin.succ_inj] at hb; subst hb; rfl)
      | (exact absurd h.1 (Fin.succ_ne_zero _))
      | (exact absurd h.2 (Fin.succ_ne_zero _))
      | (exact absurd h.1.symm (Fin.succ_ne_zero _))
      | (exact absurd h.2.symm (Fin.succ_ne_zero _))

/-- The bg-shift matrix `g·bᵀ` from the `(g,b)`-cube `v : Fin m ⊕ Fin m → ℝ`:
`bgShiftG v a b = v (inl a) · v (inr b)` (the rank-1 Cramer shift, `M21·M11⁻¹·M12` at `j=1`). -/
noncomputable def bgShiftG (m : ℕ) (v : Fin m ⊕ Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun a b => v (Sum.inl a) * v (Sum.inr b)

theorem bgShiftG_entry_le (m : ℕ) (v : Fin m ⊕ Fin m → ℝ) (hv : ∀ s, |v s| ≤ 1) (a b : Fin m) :
    |bgShiftG m v a b| ≤ 1 := by
  rw [bgShiftG, abs_mul]
  calc |v (Sum.inl a)| * |v (Sum.inr b)| ≤ 1 * 1 :=
        mul_le_mul (hv _) (hv _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The defining spec of `slotMatG` on a non-`(0,0)` cell: `(finCongr hN p).succAbove (slotMatG … a b)
= finCongr hN (eG r (σr a, σc b))` (the `Fin N`-slot decodes to the cell's flattened index). The bijection
keystone (`Fin N ≃ {non-pivot cells}` via `succAbove`/`finCongr`/`eG`). -/
theorem slotMatG_spec (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r)) (a b : Fin r)
    (hab : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩)) :
    (finCongr hN p).succAbove (slotMatG r N hN hr p a b)
      = finCongr hN (eG r ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) a,
          (Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) b)) := by
  have hidx : eG r ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) a,
      (Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) b) ≠ p :=
    RmatGnorm_offpivot_idx r hr p a b hab
  have hne : finCongr hN (eG r ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) a,
      (Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) b)) ≠ finCongr hN p :=
    fun he => hidx ((finCongr hN).injective he)
  rw [slotMatG, dif_pos hidx]
  exact (Fin.exists_succAbove_eq hne).choose_spec

/-- The off-`(0,0)` cell of `Fin r × Fin r` for a carve-slot, in the firing's `Fin r` world (NOT
`cellOfG`'s `Fin ((r-1)+1)`, which forces a cast): `M22 (a,b) ↦ (a+1, b+1)`, `g a ↦ (a+1, 0)`,
`b b ↦ (0, b+1)`. The `Fin r`-native cell enumeration for the `zEG` carve. -/
noncomputable def cellR (r : ℕ) (hr : 3 ≤ r) :
    (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) → Fin r × Fin r
  | Sum.inl (a, b) => (⟨(a : ℕ) + 1, by omega⟩, ⟨(b : ℕ) + 1, by omega⟩)
  | Sum.inr (Sum.inl a) => (⟨(a : ℕ) + 1, by omega⟩, ⟨0, by omega⟩)
  | Sum.inr (Sum.inr b) => (⟨0, by omega⟩, ⟨(b : ℕ) + 1, by omega⟩)

/-- `cellR` lands on non-`(0,0)` cells. -/
theorem cellR_ne_zero (r : ℕ) (hr : 3 ≤ r) (s : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1))) :
    ¬ ((cellR r hr s).1 = ⟨0, by omega⟩ ∧ (cellR r hr s).2 = ⟨0, by omega⟩) := by
  rcases s with ⟨a, b⟩ | (a | b) <;> simp [cellR, Fin.ext_iff]

/-- `cellR` is injective. -/
theorem cellR_injective (r : ℕ) (hr : 3 ≤ r) : Function.Injective (cellR r hr) := by
  rintro (⟨a1, b1⟩ | (a1 | b1)) (⟨a2, b2⟩ | (a2 | b2)) h <;>
    simp only [cellR, Prod.mk.injEq, Fin.ext_iff] at h
  · obtain ⟨h1, h2⟩ := h
    have ea : a1 = a2 := Fin.ext (by omega)
    have eb : b1 = b2 := Fin.ext (by omega)
    subst ea; subst eb; rfl
  · omega
  · omega
  · omega
  · have ea : a1 = a2 := Fin.ext (by omega); subst ea; rfl
  · omega
  · omega
  · omega
  · have eb : b1 = b2 := Fin.ext (by omega); subst eb; rfl

/-- The slot-composition `s ↦ slotMatG p (cellR s).1 (cellR s).2 : (M22 ⊕ g ⊕ b) → Fin N` is injective:
`slotMatG_spec` decodes the slot to `finCongr hN (eG (σr cell, σc cell))`, injective via
`eG`/swap/`finCongr` injectivity, then `cellR_injective`. -/
theorem slotFunR_injective (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r)) :
    Function.Injective
      (fun s : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) =>
        slotMatG r N hN hr p (cellR r hr s).1 (cellR r hr s).2) := by
  intro s1 s2 hs
  simp only [] at hs
  have e1 := slotMatG_spec r N hN hr p (cellR r hr s1).1 (cellR r hr s1).2 (cellR_ne_zero r hr s1)
  have e2 := slotMatG_spec r N hN hr p (cellR r hr s2).1 (cellR r hr s2).2 (cellR_ne_zero r hr s2)
  rw [hs, e2] at e1
  have hcell : ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) (cellR r hr s2).1,
      (Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) (cellR r hr s2).2)
      = ((Equiv.swap ((eG r).symm p).1 ⟨0, by omega⟩) (cellR r hr s1).1,
        (Equiv.swap ((eG r).symm p).2 ⟨0, by omega⟩) (cellR r hr s1).2) :=
    (eG r).injective ((finCongr hN).injective e1)
  rw [Prod.mk.injEq] at hcell
  obtain ⟨hi, hj⟩ := hcell
  exact (cellR_injective r hr
    (Prod.ext ((Equiv.swap _ _).injective hi) ((Equiv.swap _ _).injective hj))).symm

/-- The carve-slot index count `card ((M22) ⊕ (g ⊕ b)) = (r−1)² + 2(r−1) = r²−1 = N`. -/
theorem slotFunR_card (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) :
    Fintype.card ((Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1))) = N := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith [hN, Nat.sub_add_cancel (show 1 ≤ r by omega)]

/-- **The carve-slot bijection** `(M22 ⊕ g ⊕ b) ≃ Fin N`: the slot-composition is bijective (injective
+ card-matched). -/
theorem slotFunR_bijective (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r)) :
    Function.Bijective
      (fun s : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) =>
        slotMatG r N hN hr p (cellR r hr s).1 (cellR r hr s).2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨slotFunR_injective r N hN hr p, ?_⟩
  rw [Fintype.card_fin]; exact slotFunR_card r N hN hr

/-- The slot equiv `Fin N ≃ (M22 ⊕ g ⊕ b)` (`σ.symm s = slotMatG p (cellR s)…`). -/
noncomputable def zσG (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r)) :
    Fin N ≃ ((Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1))) :=
  (Equiv.ofBijective _ (slotFunR_bijective r N hN hr p)).symm

/-- The reshape `zEG : (Fin N → ℝ) ≃ᵐ ((Fin(r-1)×Fin(r-1) → ℝ) × ((Fin(r-1)⊕Fin(r-1)) → ℝ))`
splitting the ratios `z` into the `M22`-cube and the `(g,b)`-cube (`piCongrLeft zσG ≫ sumPiEquivProdPi`). -/
noncomputable def zEG (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r)) :
    (Fin N → ℝ) ≃ᵐ (((Fin (r - 1) × Fin (r - 1)) → ℝ) × ((Fin (r - 1) ⊕ Fin (r - 1)) → ℝ)) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) => ℝ) (zσG r N hN hr p)).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) => ℝ))

theorem measurePreserving_zEG (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r)) :
    MeasurePreserving (zEG r N hN hr p) (volume : Measure (Fin N → ℝ))
      (volume : Measure (((Fin (r - 1) × Fin (r - 1)) → ℝ) × ((Fin (r - 1) ⊕ Fin (r - 1)) → ℝ))) :=
  (volume_measurePreserving_piCongrLeft
    (fun _ : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) => ℝ) (zσG r N hN hr p)).trans
    (volume_measurePreserving_sumPiEquivProdPi
      (fun _ : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) => ℝ))

/-- The `zEG.symm` read-back: `(zEG.symm (M, v)) k = Sum.elim M v (zσG k)` — the carved cube entry at the
slot `zσG k`. The keystone for the `Sc = matOf M22 − bgShiftG (g,b)` carve readback. -/
theorem zEG_symm_apply (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r))
    (M : (Fin (r - 1) × Fin (r - 1)) → ℝ) (v : (Fin (r - 1) ⊕ Fin (r - 1)) → ℝ) (k : Fin N) :
    (zEG r N hN hr p).symm (M, v) k = Sum.elim M v (zσG r N hN hr p k) := by
  have hdec : (zEG r N hN hr p).symm (M, v)
      = (MeasurableEquiv.piCongrLeft
          (fun _ : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) => ℝ)
          (zσG r N hN hr p)).symm (Sum.elim M v) := rfl
  rw [hdec]
  set e := zσG r N hN hr p
  have h1 : MeasurableEquiv.piCongrLeft
      (fun _ : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) => ℝ) e
      ((MeasurableEquiv.piCongrLeft
        (fun _ : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1)) => ℝ) e).symm
        (Sum.elim M v)) (e k) = Sum.elim M v (e k) := by
    rw [MeasurableEquiv.apply_symm_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply] at h1
  exact h1

/-- `zσG` round-trips on the slot of a cell: `zσG (slotMatG p (cellR s).1 (cellR s).2) = s`. -/
theorem zσG_slot (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r) (p : Fin (r * r))
    (s : (Fin (r - 1) × Fin (r - 1)) ⊕ (Fin (r - 1) ⊕ Fin (r - 1))) :
    zσG r N hN hr p (slotMatG r N hN hr p (cellR r hr s).1 (cellR r hr s).2) = s :=
  (Equiv.ofBijective _ (slotFunR_bijective r N hN hr p)).symm_apply_apply s

/-- **The generic ratio-residual (the firing heart, mid case `2 < c' < λ_r`).** The JOINT integral over
the `r²−1` angular ratios `z` (pivot axis set to `0` via `piRatioG`) and `S` is finite for
`2 < c' < λ_r`, `r ≥ 3`: per `z` the angular `RmatG r p ((piRatioG …).symm (0,z))` has pivot `1`,
`|entries| ≤ 1`; N2b (`j = 1`) peels the top `Fin 4` Morse block (threshold `2`), leaving the residual at
`c'' = c' − 2 ∈ (0, λ_{r−1})`; the `M22 ↦ Sc` carving + the lower IH `hIH` (via
`schurResidG_translate_lt_top`) close it. The genuinely-new generic content. `N = r²−1`
(so `r * r = N + 1`). -/
theorem schurRatioResidGen_mid (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc2 : 2 < c') (hc' : c' < schurLambda r)
    (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGen r c' T p ((piRatioG r N hN p).symm (0, z)))
      < ⊤ := by
  -- DEFERRED (the sole remaining R1-UPPER input): the per-`z` N2b → Morse-peel → carve assembly.
  -- The IH-invoking carving CORE `schurResidG_translate_lt_top` is PROVED above; this lemma is the
  -- per-`z` glue. Codex (xhigh, decorrelated) confirmed the route — ORDER: CARVE-FIRST:
  --   pivot-WLOG (frobSq_rmatMul_permG + matBox_rowperm_lintegralG, pivot → (0,0))
  --   → carve `z` = (M22 ⊕ rest) via a generic `zE_G : (Fin N → ℝ) ≃ᵐ
  --       ((Fin (r-1) × Fin (r-1) → ℝ) × (Fin (2(r-1)) → ℝ))` with readback `Sc = M22 − Sh(rest)`
  --       (the HARDEST sub-step — the M22/M21/M12 index bijection + the Schur-formula readback)
  --   → pointwise N2b/split (`schur_minorPivot_split` j=1 — the TWO-SIDED uniform-constant comparison
  --       `c₀(frobSq row0 + frobSq(Sc·S_bot)) ≤ frobSq(R·S) ≤ c₁(…)`, NOT a constant-1 bound) + top-row shear
  --   → Tonelli + a.e. Morse peel over the FREE `(M22, S_bot)` joint core (`radial_morse_residual_power_le`,
  --       a.e.-positive by the nonzero-`MvPolynomial` argument — peel AFTER carving so positivity is clean)
  --   → `schurResidG_translate_lt_top` per fixed `rest` at exponent `c' − 2` and residual radius
  --       `K = max 1 T` (M22 box radius 1, S_bot box radius T — Codex radius fix), `B = 1` (|Sh| ≤ 1)
  --   → the outer bounded-`rest`-box volume is a finite constant.
  -- A standalone `resolvedShiftRG_le` (generic analog of `resolvedShiftR2c3_le`) is the recommended next
  -- brick. ~200 generic-r lines; well-scoped, no design wall (all ingredients PROVED/CONFIRMED).
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
  -- `3 ∈ (2, λ_r)` for `r ≥ 3` (λ_r = 2r−2 ≥ 4)
  have h3lt : (3 : ℝ) < schurLambda r := by
    rw [schurLambda_eq_of_ge_two (by omega)]
    have : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rcases lt_or_ge 2 c' with hc2 | hc2
  · exact schurRatioResidGen_mid r N hN hr hIH c' hc2 hc' p T hT
  · -- c' ≤ 2: dominate the inner integrand by `1 + (·)^{−3}`, reduce to the c'' = 3 mid case
    set q : (Fin N → ℝ) → (Fin (r * r) → ℝ) := fun z => (piRatioG r N hN p).symm (0, z) with hq
    -- per z: innerSGen c' (q z) ≤ vol(matBox r 4 T) + innerSGen 3 (q z)
    have hdom : ∀ z : Fin N → ℝ,
        innerSGen r c' T p (q z)
          ≤ volume (matBox r 4 T) + innerSGen r 3 T p (q z) := by
      intro z
      rw [innerSGen, innerSGen]
      calc (∫⁻ S in matBox r 4 T,
              ENNReal.ofReal ((frobSq (rmatMul (RmatG r p (q z)) S)) ^ (-c')))
          ≤ ∫⁻ S in matBox r 4 T,
              (1 + ENNReal.ofReal ((frobSq (rmatMul (RmatG r p (q z)) S)) ^ (-(3 : ℝ)))) :=
            lintegral_mono (fun S =>
              ofReal_rpow_neg_le_one_addG _ (frobSq_nonneg _) c' 3 hc0 (by linarith))
        _ = volume (matBox r 4 T) + ∫⁻ S in matBox r 4 T,
              ENNReal.ofReal ((frobSq (rmatMul (RmatG r p (q z)) S)) ^ (-(3 : ℝ))) := by
            rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    refine lt_of_le_of_lt (lintegral_mono hdom) ?_
    rw [lintegral_add_left measurable_const, setLIntegral_const]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top (matBox_volume_lt_top r 4 T)
        (by rw [show (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)) = morseBox N 1 from by
          rw [morseBox]]; exact morseBox_volume_lt_top N 1)
    · exact schurRatioResidGen_mid r N hN hr hIH 3 (by norm_num) h3lt p T hT

/-- The chart integrand factors as `radInd(y p) · innerSGen` (`|y p|^{r²−1} → |y p|^{(r²−1)−2c'}` via
the radial peel, `y p ≠ 0` from `\ pivotZeroOn`). Mirror of `chart_integrand_factor3` at generic `r`. -/
theorem chart_integrand_factorG (r : ℕ) (c' : ℝ) (hc0 : 0 < c') (T : ℝ) (hT : 0 < T)
    (p : Fin (r * r)) (y : Fin (r * r) → ℝ) (hyp0 : y p ≠ 0)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (r * r))) p) :
    ENNReal.ofReal (|y p| ^ (r * r - 1))
        * (flatBoxG r T).indicator (gFlatG r c' T) (pivotBlowupOn
            (Finset.univ : Finset (Fin (r * r))) p y)
      = (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) (y p)
        * innerSGen r c' T p y := by
  by_cases hmem : pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y ∈ flatBoxG r T
  · have hyp : |y p| ≤ T := (flatBoxG_blowup_mem_iff r T p y hy).1 hmem
    rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (s := Set.Icc (-T) T) (by rw [Set.mem_Icc, ← abs_le]; exact hyp)]
    rw [gFlatG_blowup_radial r c' T p y, innerSGen]
    have hpull : ∀ S : Fin r → Fin 4 → ℝ,
        ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (RmatG r p y) S)) ^ (-c'))
          = ENNReal.ofReal ((((y p) ^ 2) ^ (-c')))
            * ENNReal.ofReal ((frobSq (rmatMul (RmatG r p y) S)) ^ (-c')) := by
      intro S
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ← Real.mul_rpow (by positivity) (frobSq_nonneg _)]
    rw [lintegral_congr hpull, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hb : ((y p) ^ 2 : ℝ) = |y p| ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hpos : (0 : ℝ) < |y p| := abs_pos.2 hyp0
    rw [hb, ← Real.rpow_natCast (|y p|) (r * r - 1), ← Real.rpow_mul (le_of_lt hpos),
      ← Real.rpow_add hpos]
    congr 1; push_cast; ring
  · have hyp : ¬ |y p| ≤ T := fun h => hmem ((flatBoxG_blowup_mem_iff r T p y hy).2 h)
    rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (s := Set.Icc (-T) T)
        (by rw [Set.mem_Icc, ← abs_le]; exact hyp), zero_mul, mul_zero]

/-- **The generic per-chart finiteness.** Mirror of `matBox3_chart_lt_top` at generic `r`: the radial
blow-up chart integral (Jacobian `|y p|^{r²−1}`) is finite for `0 < c' < λ_r`, `r ≥ 3`. The `piRatioG`
MP + Tonelli factor the pivot axis (a-axis divisor finite for `c' < r²/2`, holds since `c' < λ_r ≤ r²/2`)
from the `r²−1` ratios; the ratio residual is `schurRatioResidGen`. -/
theorem schur_matBoxG_chart_lt_top (r : ℕ) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambda r)
    (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (r * r))) p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) p y).det|
          * (flatBoxG r T).indicator (gFlatG r c' T) (pivotBlowupOn
              (Finset.univ : Finset (Fin (r * r))) p y)
      < ⊤ := by
  have hrr : 0 < r * r := by positivity
  obtain ⟨N, hN⟩ : ∃ N, r * r = N + 1 := ⟨r * r - 1, by omega⟩
  -- thresholds, in `r` form
  have hlamr : schurLambda r ≤ (r ^ 2 : ℝ) / 2 := schurLambda_le_sq r
  -- |det| = |y p|^{r²−1}
  have hdet : ∀ y : Fin (r * r) → ℝ,
      |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) p y).det| = |y p| ^ (r * r - 1) := by
    intro y
    rw [pivotBlowupOnDeriv_det (Finset.univ : Finset (Fin (r * r))) p (Finset.mem_univ p) y,
      Finset.card_univ, Fintype.card_fin]
    simp [abs_pow]
  simp only [hdet]
  -- the chart domain is measurable
  have hmsD : MeasurableSet (chartDomOn (Finset.univ : Finset (Fin (r * r))) p \ pivotZeroOn p) := by
    refine MeasurableSet.diff ?_ ?_
    · have heq : chartDomOn (Finset.univ : Finset (Fin (r * r))) p
          = ⋂ k ∈ (Finset.univ.erase p), {y : Fin (r * r) → ℝ | |y k| ≤ 1} := by
        ext y
        simp only [chartDomOn, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_erase,
          Finset.mem_univ, true_and, and_true, true_implies]
      rw [heq]
      refine Finset.measurableSet_biInter (Finset.univ.erase p) (fun k _ => ?_)
      exact measurableSet_le ((measurable_pi_apply k).abs) measurable_const
    · exact (measurable_pi_apply p (measurableSet_singleton 0))
  rw [setLIntegral_congr_fun hmsD (fun y hy => chart_integrand_factorG r c' hc0 T hT p y hy.2 hy.1)]
  -- reshape Fin(r*r)→ℝ ≃ ℝ × (Fin N → ℝ) via piRatioG
  set e := piRatioG r N hN p with he
  have hmp : MeasurePreserving e (volume) (volume) := measurePreserving_piRatioG r N hN p
  -- the chart domain pulls back to ({a ≠ 0}) ×ˢ (ratio box over Fin N)
  have hpre : (chartDomOn (Finset.univ : Finset (Fin (r * r))) p \ pivotZeroOn p)
      = e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))) := by
    ext y
    simp only [chartDomOn, pivotZeroOn, Set.mem_diff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, he]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [piRatioG_apply_fst]; exact h2, fun j => ?_⟩
      rw [Set.mem_Icc, ← abs_le, piRatioG_apply_snd]
      exact h1 _ (Finset.mem_univ _) (piRatioG_ratioIdx_ne r N hN p j)
    · rintro ⟨h1, h2⟩
      rw [piRatioG_apply_fst] at h1
      refine ⟨fun k _ hk => ?_, h1⟩
      -- k ≠ p decodes as a ratio index; its value is the corresponding z j ∈ [−1,1]
      have hne : finCongr hN k ≠ finCongr hN p := fun h => hk ((finCongr hN).injective h)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
      have hk_eq : k = (finCongr hN).symm ((finCongr hN p).succAbove j) := by
        rw [hj]; exact ((finCongr hN).symm_apply_apply k).symm
      have hj2 := h2 j
      rw [Set.mem_Icc, ← abs_le, piRatioG_apply_snd r N hN p y j] at hj2
      rw [hk_eq]; exact hj2
  set g : (Fin (r * r) → ℝ) → ℝ≥0∞ := fun y =>
    (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) (y p)
      * innerSGen r c' T p y with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    refine Measurable.mul ?_ (measurable_innerSGen r c' T p)
    have hind : Measurable (fun a : ℝ =>
        (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a) := by
      refine Measurable.indicator ?_ measurableSet_Icc
      exact ENNReal.measurable_ofReal.comp ((measurable_id.abs).pow_const _)
    exact hind.comp (measurable_pi_apply p)
  rw [hpre]
  have hSms : MeasurableSet
      (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))) :=
    MeasurableSet.prod (by measurability) (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  have key := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun q => g (e.symm q))
    (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)))
  have htrans : (∫⁻ y in e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ
        (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))), g y)
      = ∫⁻ q in (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))),
          g (e.symm q) := by
    rw [← key]
    refine setLIntegral_congr_fun (e.measurable hSms) (fun y _ => ?_)
    rw [MeasurableEquiv.symm_apply_apply]
  rw [htrans]
  have hgsymm_meas : Measurable (fun q : ℝ × (Fin N → ℝ) => g (e.symm q)) :=
    hgmeas.comp e.symm.measurable
  rw [Measure.volume_eq_prod ℝ (Fin N → ℝ), setLIntegral_prod _ hgsymm_meas.aemeasurable]
  -- the joint factorisation: g (e.symm (a,z)) = radInd a · innerSGen … (e.symm (0,z))
  have hfactor : ∀ a : ℝ, ∀ z : Fin N → ℝ,
      g (e.symm (a, z))
        = (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a
          * innerSGen r c' T p (e.symm (0, z)) := by
    intro a z
    have hp_eq : (e.symm (a, z)) p = a := by rw [he]; exact piRatioG_symm_pivot r N hN p a z
    have hoff : innerSGen r c' T p (e.symm (a, z)) = innerSGen r c' T p (e.symm (0, z)) := by
      refine innerSGen_offpivot r c' T p _ _ (fun i hi => ?_)
      rw [he]; exact piRatioG_symm_offpivot r N hN p a 0 z i hi
    show (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) ((e.symm (a, z)) p)
        * innerSGen r c' T p (e.symm (a, z)) = _
    rw [hp_eq, hoff]
  -- radial-axis factor finite (c' < r²/2 ⟹ exponent (r²−1)−2c' > −1)
  have hN3a : (∫⁻ a in Set.Icc (-T) T,
      ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c'))) < ⊤ :=
    radial_aAxis_divisor_lt_top r (by omega) T hT c' (by linarith [hlamr])
  have hexp : ((r ^ 2 : ℝ) - 1 - 2 * c') = (((r * r - 1 : ℕ) : ℝ) - 2 * c') := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]; push_cast [pow_two]; ring
  rw [hexp] at hN3a
  have hradfin : (∫⁻ a in {a : ℝ | a ≠ 0},
        (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a) < ⊤ := by
    have hle1 : (∫⁻ a in {a : ℝ | a ≠ 0},
          (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a)
        ≤ ∫⁻ a, (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a := by
      have := lintegral_mono_set (μ := volume) (s := {a : ℝ | a ≠ 0}) (t := Set.univ)
        (Set.subset_univ _)
        (f := (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))))
      rwa [setLIntegral_univ] at this
    have heq2 : (∫⁻ a, (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a)
        = ∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c')) :=
      lintegral_indicator measurableSet_Icc _
    rw [heq2] at hle1
    exact lt_of_le_of_lt hle1 hN3a
  -- ratio residual finite via schurRatioResidGen
  have hratiofin : (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGen r c' T p (e.symm (0, z))) < ⊤ :=
    schurRatioResidGen r N hN hr hIH c' hc0 hc' p T hT
  have hinner : ∀ a : ℝ,
      (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)), g (e.symm (a, z)))
        = (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a
          * ∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
              innerSGen r c' T p (e.symm (0, z)) := by
    intro a
    have hradne : (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a ≠ ⊤ := by
      rw [Set.indicator_apply]; split <;> simp [ENNReal.ofReal_ne_top]
    rw [lintegral_congr (fun z => hfactor a z), lintegral_const_mul' _ _ hradne]
  rw [lintegral_congr hinner, lintegral_mul_const' _ _ hratiofin.ne]
  exact ENNReal.mul_lt_top hradfin hratiofin

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
