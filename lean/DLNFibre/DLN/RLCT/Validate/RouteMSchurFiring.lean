import DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral
import DLNFibre.DLN.RLCT.Validate.RouteMSchurGenCover
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

/-! ## The generic outer radial-Δ `r²`-chart cover

The generic flatten + `r²`-chart radial cover is the CANONICAL `RouteMSchurGenCover`
(`matToFlatGen`/`flatBoxGen`/`matBoxGen_outer_flat`/`gFlatGen_cover_sum`, sorry-free, axiom-clean,
`p`-general). This file reuses it (at `p = 4`) — only the radial pull-out `RmatG`/`gFlatG_blowup_radial`
is local to the firing. -/

/-- The unflattened angular matrix on chart `p`: `RmatG p y` is the `r×r` matrix with `R_p = 1`,
`R_k = y_k` (`k ≠ p`), via the canonical flatten `matToFlatGen`. -/
noncomputable def RmatG (r : ℕ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ) : Fin r → Fin r → ℝ :=
  (matToFlatGen r).symm (fun i => if i = p then 1 else y i)

/-- **The radial pull-out** (N1 degree-2 homogeneity): `gFlatGen r 4 c' T (blowup) =
∫_S ((y p)²·frobSq(RmatG·S))^{−c'}`. -/
theorem gFlatG_blowup_radial (r : ℕ) (c' : ℝ) (T : ℝ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ) :
    gFlatGen r 4 c' T (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y)
      = ∫⁻ S in matBox r 4 T,
          ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (RmatG r p y) S)) ^ (-c')) := by
  unfold gFlatGen RmatG
  refine lintegral_congr (fun S => ?_)
  congr 1
  have hbl : (matToFlatGen r).symm (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y)
      = fun a b => (y p) * ((matToFlatGen r).symm (fun i => if i = p then 1 else y i)) a b := by
    funext a b
    show (matToFlatGen r).symm (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y) a b = _
    rw [show pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y
        = (fun i => (y p) * (if i = p then 1 else y i)) from by
      funext i; unfold pivotBlowupOn
      by_cases hi : i = p
      · subst hi; simp
      · simp [hi]]
    rfl
  rw [hbl, radialDelta_loss_factor (y p) ((matToFlatGen r).symm (fun i => if i = p then 1 else y i)) S]

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

/-- The matrix↔flat index equiv `eG r : Fin r × Fin r ≃ Fin (r*r)`, matching `matToFlatGen`'s index reindex. -/
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

/-- On the chart, the blown-up point lands in `flatBoxGen r T` IFF `|y p| ≤ T`. -/
theorem flatBoxG_blowup_mem_iff (r : ℕ) (T : ℝ) (p : Fin (r * r)) (y : Fin (r * r) → ℝ)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (r * r))) p) :
    pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y ∈ flatBoxGen r T ↔ |y p| ≤ T := by
  unfold flatBoxGen chartDomOn at *
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

/-! ### The generic joint-core a.e.-positivity (the Morse-peel's `0 < w` hypothesis)

After the carve, the Morse peel sees the FREE `(Δ, S)` joint corank-`m` core (`m = r−1`); it needs
`frobSq (Δ·S) > 0` a.e. The core is a nonzero polynomial in the flattened `(Δ,S)` coords (witness `Δ = I_m`,
`S = e₁` gives core `= 1`), so its zero set is null (`MvPolynomial.ae_eval_ne_zero`). Generic analog of
`RouteMSchurCorank3.frobSqR2c3_ne_zero_ae`. -/

/-- The joint corank-`m` residual core as an `MvPolynomial ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) ℝ`
(Δ-coords `inl (i,k)`, S-coords `inr (k,j)`) — the `frobSq (Δ·S)` polynomial. Indexing by the product
type (NOT `Fin N` div/mod) keeps the eval readback `rfl`-clean. -/
noncomputable def corePolyGen (m : ℕ) :
    MvPolynomial ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) ℝ :=
  ∑ i : Fin m, ∑ j : Fin 4,
    (∑ k : Fin m,
      (MvPolynomial.X (Sum.inl (i, k)) * MvPolynomial.X (Sum.inr (k, j)))) ^ 2

/-- The flatten `(Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) → (((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ)`
(Δ → `inl`, S → `inr`) — the eval-variable assignment for `corePolyGen`. -/
noncomputable def flatGenJoint (m : ℕ) (q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)) :
    ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ :=
  Sum.elim (fun ik => q.1 ik.1 ik.2) (fun kj => q.2 kj.1 kj.2)

/-- `eval (flatGenJoint m q) (corePolyGen m) = frobSq (q.1 · q.2)`. -/
theorem eval_corePolyGen (m : ℕ) (q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)) :
    MvPolynomial.eval (flatGenJoint m q) (corePolyGen m) = frobSq (rmatMul q.1 q.2) := by
  rw [corePolyGen]
  unfold frobSq rmatMul flatGenJoint
  simp only [map_sum, map_pow, map_mul, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]

open MvPolynomial in
/-- `corePolyGen m ≠ 0` for `m ≥ 1` (witness `Δ = I_m`, `S = e₁` ⟹ core `= 1`). -/
theorem corePolyGen_ne_zero (m : ℕ) (hm : 1 ≤ m) : corePolyGen m ≠ 0 := by
  intro h0
  -- witness assignment: Δ = identity (inl (i,k) ↦ if i=k then 1 else 0), S = e₁ (inr (k,j) ↦ if k=0∧j=0 then 1 else 0)
  set w : ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ :=
    Sum.elim (fun ik => if ik.1 = ik.2 then (1:ℝ) else 0)
      (fun kj => if kj.1 = ⟨0, by omega⟩ ∧ kj.2 = 0 then (1:ℝ) else 0) with hw
  have hval : MvPolynomial.eval w (corePolyGen m) = 1 := by
    have hq : flatGenJoint m
        (⟨fun i k => if i = k then (1:ℝ) else 0,
          fun k j => if k = ⟨0, by omega⟩ ∧ j = 0 then (1:ℝ) else 0⟩
          : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)) = w := by
      funext c; cases c with
      | inl ik => rfl
      | inr kj => rfl
    rw [← hq, eval_corePolyGen]
    -- frobSq(I·e₁) = 1: (I·e₁)_{ij} = e₁_{ij} = [i=0∧j=0]; frobSq = 1
    unfold frobSq rmatMul
    have hentry : ∀ i : Fin m, ∀ j : Fin 4,
        (∑ k, (if i = k then (1:ℝ) else 0) * (if k = ⟨0, by omega⟩ ∧ j = 0 then (1:ℝ) else 0))
          = if i = ⟨0, by omega⟩ ∧ j = 0 then (1:ℝ) else 0 := by
      intro i j
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; rw [if_neg (Ne.symm hk), zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [show (∑ i : Fin m, ∑ j : Fin 4,
        (∑ k, (if i = k then (1:ℝ) else 0) * (if k = ⟨0, by omega⟩ ∧ j = 0 then (1:ℝ) else 0)) ^ 2)
        = ∑ i : Fin m, ∑ j : Fin 4,
          (if i = ⟨0, by omega⟩ ∧ j = 0 then (1:ℝ) else 0) ^ 2 from by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hentry i j]]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin m)]
    · rw [Finset.sum_eq_single (0 : Fin 4)]
      · simp
      · intro j _ hj; simp [hj]
      · intro hj; exact absurd (Finset.mem_univ _) hj
    · intro i _ hi; refine Finset.sum_eq_zero (fun j _ => ?_); simp [hi]
    · intro hi; exact absurd (Finset.mem_univ _) hi
  rw [h0] at hval; simp at hval

/-- The measure-preserving flatten `(Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) ≃ᵐ ((Sum type) → ℝ)`,
matching `flatGenJoint` (Δ-curry to `Fin m × Fin m`, S-curry to `Fin m × Fin 4`, glue by
`sumPiEquivProdPi.symm`). -/
noncomputable def flatGenJointEquiv (m : ℕ) :
    ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)) ≃ᵐ (((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ) :=
  (MeasurableEquiv.prodCongr
    ((MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin m) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' (Equiv.sigmaEquivProd (Fin m) (Fin m)) (MeasurableEquiv.refl ℝ)))
    ((MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin 4) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' (Equiv.sigmaEquivProd (Fin m) (Fin 4))
        (MeasurableEquiv.refl ℝ)))).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin 4) => ℝ)).symm

theorem measurePreserving_flatGenJointEquiv (m : ℕ) :
    MeasurePreserving (flatGenJointEquiv m)
      (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)))
      (volume : Measure (((Fin m × Fin m) ⊕ (Fin m × Fin 4)) → ℝ)) := by
  unfold flatGenJointEquiv
  -- MP of the two curry factors
  have hΔ : MeasurePreserving
      ((MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin m) => ℝ)).symm.trans
        (MeasurableEquiv.arrowCongr' (Equiv.sigmaEquivProd (Fin m) (Fin m)) (MeasurableEquiv.refl ℝ)))
      (volume : Measure (Fin m → Fin m → ℝ)) (volume : Measure (Fin m × Fin m → ℝ)) := by
    refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
      (Equiv.sigmaEquivProd (Fin m) (Fin m)) (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
    exact (measurePreserving_piCurry (fun (_ : Fin m) (_ : Fin m) => ℝ)
      (fun _ _ => (volume : Measure ℝ))).symm (MeasurableEquiv.piCurry _)
  have hS : MeasurePreserving
      ((MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin 4) => ℝ)).symm.trans
        (MeasurableEquiv.arrowCongr' (Equiv.sigmaEquivProd (Fin m) (Fin 4)) (MeasurableEquiv.refl ℝ)))
      (volume : Measure (Fin m → Fin 4 → ℝ)) (volume : Measure (Fin m × Fin 4 → ℝ)) := by
    refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
      (Equiv.sigmaEquivProd (Fin m) (Fin 4)) (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
    exact (measurePreserving_piCurry (fun (_ : Fin m) (_ : Fin 4) => ℝ)
      (fun _ _ => (volume : Measure ℝ))).symm (MeasurableEquiv.piCurry _)
  have hprod : MeasurePreserving
      (MeasurableEquiv.prodCongr
        ((MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin m) => ℝ)).symm.trans
          (MeasurableEquiv.arrowCongr' (Equiv.sigmaEquivProd (Fin m) (Fin m)) (MeasurableEquiv.refl ℝ)))
        ((MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin 4) => ℝ)).symm.trans
          (MeasurableEquiv.arrowCongr' (Equiv.sigmaEquivProd (Fin m) (Fin 4)) (MeasurableEquiv.refl ℝ))))
      (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)))
      (volume : Measure ((Fin m × Fin m → ℝ) × (Fin m × Fin 4 → ℝ))) := by
    rw [show (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)))
        = volume.prod volume from rfl,
      show (volume : Measure ((Fin m × Fin m → ℝ) × (Fin m × Fin 4 → ℝ)))
        = volume.prod volume from rfl]
    exact hΔ.prod hS
  exact hprod.trans
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : (Fin m × Fin m) ⊕ (Fin m × Fin 4) => ℝ))

theorem flatGenJointEquiv_apply (m : ℕ) (q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)) :
    flatGenJointEquiv m q = flatGenJoint m q := by
  funext c; cases c with
  | inl ik => rfl
  | inr kj => rfl

open MvPolynomial in
/-- **The generic joint corank-`m` residual core is positive a.e.** `∀ᵐ (Δ,S), 0 < frobSq (Δ·S)` for
`m ≥ 1` (the Morse-peel's `0 < w` hypothesis). The core is a nonzero polynomial (`corePolyGen_ne_zero`),
so its zero set is null (`MvPolynomial.ae_eval_ne_zero` — transported to `Fin n` via the Fintype-equiv
`rename`), pulled back along the measure-preserving `flatGenJointEquiv`. Generic analog of
`frobSqR2c3_ne_zero_ae`. -/
theorem frobSqGenJoint_ne_zero_ae (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) ∂(volume),
      0 < frobSq (rmatMul q.1 q.2) := by
  -- transport corePolyGen (Sum-indexed) to Fin n via the Fintype equiv, apply ae_eval_ne_zero
  set σ : ((Fin m × Fin m) ⊕ (Fin m × Fin 4)) ≃ Fin (Fintype.card ((Fin m × Fin m) ⊕ (Fin m × Fin 4))) :=
    Fintype.equivFin _ with hσ
  set pFin : MvPolynomial (Fin (Fintype.card ((Fin m × Fin m) ⊕ (Fin m × Fin 4)))) ℝ :=
    MvPolynomial.rename σ (corePolyGen m) with hpFin
  have hpFin_ne : pFin ≠ 0 := by
    rw [hpFin]
    simp only [ne_eq, MvPolynomial.rename_eq_zero_iff_of_injective _ σ.injective]
    exact corePolyGen_ne_zero m hm
  have hae_fin : ∀ᵐ x : Fin (Fintype.card ((Fin m × Fin m) ⊕ (Fin m × Fin 4))) → ℝ,
      MvPolynomial.eval x pFin ≠ 0 := MvPolynomial.ae_eval_ne_zero pFin hpFin_ne
  have hmsFin : MeasurableSet {x : Fin (Fintype.card ((Fin m × Fin m) ⊕ (Fin m × Fin 4))) → ℝ |
      MvPolynomial.eval x pFin ≠ 0} :=
    (MvPolynomial.measurableSet_zeroSet pFin).compl.congr (by ext x; simp)
  -- the SINGLE composite MP transport `(Δ,S) ≃ᵐ (Fin n → ℝ)`
  set Φ := (flatGenJointEquiv m).trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (Fintype.card ((Fin m × Fin m) ⊕ (Fin m × Fin 4))) => ℝ) σ) with hΦ
  have hmpΦ : MeasurePreserving Φ
      (volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ)))
      (volume : Measure (Fin (Fintype.card ((Fin m × Fin m) ⊕ (Fin m × Fin 4))) → ℝ)) :=
    (measurePreserving_flatGenJointEquiv m).trans
      (volume_measurePreserving_piCongrLeft
        (fun _ : Fin (Fintype.card ((Fin m × Fin m) ⊕ (Fin m × Fin 4))) => ℝ) σ)
  have hpull : ∀ᵐ q : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) ∂(volume),
      MvPolynomial.eval (Φ q) pFin ≠ 0 :=
    (ae_map_iff hmpΦ.measurable.aemeasurable hmsFin).1 (by rw [hmpΦ.map_eq]; exact hae_fin)
  refine hpull.mono (fun q hq => ?_)
  -- eval (Φ q) pFin = eval ((Φ q) ∘ σ) corePolyGen = eval (flatGenJointEquiv q) corePolyGen = frobSq
  rw [hpFin, MvPolynomial.eval_rename] at hq
  have hcomp : (Φ q) ∘ σ = flatGenJointEquiv m q := by
    funext s
    have : Φ q = MeasurableEquiv.piCongrLeft
        (fun _ : Fin (Fintype.card ((Fin m × Fin m) ⊕ (Fin m × Fin 4))) => ℝ) σ
        (flatGenJointEquiv m q) := rfl
    show (Φ q) (σ s) = flatGenJointEquiv m q s
    rw [this, MeasurableEquiv.piCongrLeft_apply_apply]
  rw [hcomp, flatGenJointEquiv_apply, eval_corePolyGen] at hq
  exact lt_of_le_of_ne (frobSq_nonneg _) (Ne.symm hq)

/-- **The SHIFTED generic core is positive a.e.** `∀ᵐ (Δ,S), 0 < frobSq ((Δ − Sh)·S)` for any fixed shift
`Sh : Fin m → Fin m → ℝ`, `m ≥ 1`: the translation `Δ ↦ Δ + Sh` (measure-preserving) pulls the unshifted
`frobSqGenJoint_ne_zero_ae` back. The peel's `0 < w` hypothesis at the per-`Sh` carve slice. Generic analog
of `frobSqShiftR2c3_ne_zero_ae`. -/
theorem frobSqShiftGen_ne_zero_ae (m : ℕ) (hm : 1 ≤ m) (Sh : Fin m → Fin m → ℝ) :
    ∀ᵐ p : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) ∂(volume),
      0 < frobSq (rmatMul (fun i j => p.1 i j - Sh i j) p.2) := by
  set τ : (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) → (Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ) :=
    fun p => (p.1 + (fun i j => -Sh i j), p.2) with hτ
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
    rw [hmp.map_eq]; exact frobSqGenJoint_ne_zero_ae m hm
  have hpull : ∀ᵐ p ∂(volume : Measure ((Fin m → Fin m → ℝ) × (Fin m → Fin 4 → ℝ))),
      0 < frobSq (rmatMul (τ p).1 (τ p).2) :=
    (ae_map_iff hmp.measurable.aemeasurable hmsSet).1 hae
  refine hpull.mono (fun p hp => ?_)
  have hΔeq : (τ p).1 = (fun i j => p.1 i j - Sh i j) := by
    funext i j; show (p.1 + (fun i j => -Sh i j)) i j = p.1 i j - Sh i j
    simp [Pi.add_apply, sub_eq_add_neg]
  have hSeq : (τ p).2 = p.2 := rfl
  rw [hΔeq, hSeq] at hp
  exact hp

/-! ### The slot bijection `cellOfG` (the M22/g/b cell enumeration, `m`-ambient)

The carving carves the `r²−1` non-pivot cells of the `(0,0)`-pivot `Fin (m+1) × Fin (m+1)` matrix
(`m = r−1`) into the `M22` block ⊕ the `g` (=M21 col) ⊕ the `b` (=M12 row): `(m)² + m + m = (m+1)²−1`.
`cellOfG` is the explicit enumeration (analog of corank-3 `cellOf`), injective onto the non-pivot cells. -/

/-- The non-pivot cell of `Fin (m+1) × Fin (m+1)` for a carve-slot: `M22 (a,b) ↦ (a.succ, b.succ)`,
`g a ↦ (a.succ, 0)`, `b b ↦ (0, b.succ)`. -/
def cellOfG (m : ℕ) : (Fin m × Fin m) ⊕ (Fin m ⊕ Fin m) → Fin (m + 1) × Fin (m + 1)
  | Sum.inl (a, b) => (a.succ, b.succ)
  | Sum.inr (Sum.inl a) => (a.succ, 0)
  | Sum.inr (Sum.inr b) => (0, b.succ)

/-- `cellOfG` lands on non-pivot cells (never `(0,0)`). -/
theorem cellOfG_ne_zero (m : ℕ) (s : (Fin m × Fin m) ⊕ (Fin m ⊕ Fin m)) :
    ¬ ((cellOfG m s).1 = 0 ∧ (cellOfG m s).2 = 0) := by
  rcases s with ⟨a, b⟩ | (a | b) <;> simp [cellOfG, Fin.succ_ne_zero]

/-- `cellOfG` is injective (the `m+1` cells are distinct). -/
theorem cellOfG_injective (m : ℕ) : Function.Injective (cellOfG m) := by
  rintro (⟨a1, b1⟩ | (a1 | b1)) (⟨a2, b2⟩ | (a2 | b2)) h <;>
    simp only [cellOfG, Prod.mk.injEq] at h
  · obtain ⟨ha, hb⟩ := h; rw [Fin.succ_inj] at ha hb; subst ha; subst hb; rfl
  · exact absurd h.2 (Fin.succ_ne_zero b1)
  · exact absurd h.1 (Fin.succ_ne_zero a1)
  · exact absurd h.2.symm (Fin.succ_ne_zero b2)
  · obtain ⟨ha, _⟩ := h; rw [Fin.succ_inj] at ha; subst ha; rfl
  · exact absurd h.1 (Fin.succ_ne_zero a1)
  · exact absurd h.1.symm (Fin.succ_ne_zero a2)
  · exact absurd h.1.symm (Fin.succ_ne_zero a2)
  · obtain ⟨_, hb⟩ := h; rw [Fin.succ_inj] at hb; subst hb; rfl

/-! ### The pivot-(0,0) Schur readback `Sc = M22 − M21·M12` (the carving's algebra, `m`-ambient)

The N2b (`j = 1`) Schur complement at a `(0,0)`-pivot `R : Fin (m+1) → Fin (m+1) → ℝ` (`R 0 0 = 1`):
`M11 = [1]` (`1×1`), so `M11⁻¹ = [1]` EXACTLY, and `Sc = M22 − M21·M12` is the entrywise outer-product
de-shift `Sc a b = R a.succ b.succ − R a.succ 0 · R 0 b.succ`. Parametrising by `m` (ambient `Fin (m+1)`)
dodges the `Fin r` `0`/`succ` cast-friction (Codex's mitigation). -/

/-- The `1×1` top-left minor of a `(0,0)`-pivot matrix is the identity, so its inverse is the identity. -/
theorem pivotMinor_inv_one {m : ℕ} (R : Fin (m + 1) → Fin (m + 1) → ℝ)
    (h00 : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) :
    (Matrix.of (fun a b : Fin 1 => R ⟨a, by omega⟩ ⟨b, by omega⟩))⁻¹
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have h1 : (Matrix.of (fun a b : Fin 1 => R ⟨a, by omega⟩ ⟨b, by omega⟩))
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j; fin_cases i; fin_cases j
    show R ⟨0, by omega⟩ ⟨0, by omega⟩ = (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
    rw [Matrix.one_apply_eq]; exact h00
  rw [h1, inv_one]

/-- **The N2b `j = 1` Schur readback** at a `(0,0)`-pivot `R : Fin (m+1) → Fin (m+1) → ℝ`: the genuine
Schur complement `M22 − M21·M11⁻¹·M12` equals the entrywise outer-product de-shift
`Sc a b = R ⟨1+a⟩ ⟨1+b⟩ − R ⟨1+a⟩ 0 · R 0 ⟨1+b⟩` (since `M11⁻¹ = [1]`, `pivotMinor_inv_one`). The
`M22 ↦ Sc` shift is `Sh a b = R ⟨1+a⟩ 0 · R 0 ⟨1+b⟩` (the outer product `M21·M12`). -/
theorem schurSc_readback {m : ℕ} (R : Fin (m + 1) → Fin (m + 1) → ℝ)
    (h00 : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) (a b : Fin m) :
    ((Matrix.of (fun a b : Fin m => R ⟨1 + a, by omega⟩ ⟨1 + b, by omega⟩))
      - (Matrix.of (fun (a : Fin m) (b : Fin 1) => R ⟨1 + a, by omega⟩ ⟨b, by omega⟩))
        * (Matrix.of (fun a b : Fin 1 => R ⟨a, by omega⟩ ⟨b, by omega⟩))⁻¹
        * (Matrix.of (fun (a : Fin 1) (b : Fin m) => R ⟨a, by omega⟩ ⟨1 + b, by omega⟩))) a b
      = R ⟨1 + a, by omega⟩ ⟨1 + b, by omega⟩
        - R ⟨1 + a, by omega⟩ ⟨0, by omega⟩ * R ⟨0, by omega⟩ ⟨1 + b, by omega⟩ := by
  rw [pivotMinor_inv_one R h00, Matrix.mul_one]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one, Fin.val_zero]

/-! ### The carving core — the residual translate-domination into the abstract lower IH

After N2b (`j = 1`) + the shifted `Fin 4` Morse peel, the corank-`r` ratio-residual reduces to the
corank-`(r−1)` JOINT core `∫_{Δ free}∫_{S} frobSq ((Δ − Sh)·S)^{−c''}` at the SHIFTED exponent `c'' =
c' − 2`, with `Δ` the free `(r−1)×(r−1)` block (the `M22` carved from the ratios) and `Sh` the fixed
Cramer shift (`|Sh| ≤ B`). The `Δ ↦ Δ − Sh` matrix-space translation (Jac ≡ 1) box-enlarges `Δ` to radius
`K + B`, and the ABSTRACT lower IH `SchurLowerIH 4 schurLambda r` at corank `r − 1`, radius `K + B`, closes
it (`c'' < λ_{r−1}`). The generic analog of `RouteMSchurCorank3.schurResid2_translate_le`, invoking the IH
instead of the banked `core_schur2_lt_top`. -/

/-- **The a.e. Tonelli `T`-peel bound (generic `m`).** With `w > 0` only a.e. on `Z`, the joint Morse-block
peel `∫_z ∫_T (∑Tᵢ² + w z)^{−c'} ≤ Cresid·∫_z (w z)^{−(c'−(m+1)/2)}`. Local copy of
`RouteM334Hfin.core_T_peel_le_ae` (avoiding that file's unrelated `sorry`); built on the imported
`radial_morse_residual_power_le`. The Morse-peel-under-integral the carve-first assembly consumes (peel
AFTER carving, over the FREE `(M22, S_bot)` joint core, where `w > 0` a.e. by the nonzero-poly argument). -/
theorem core_T_peel_le_ae_G {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top

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

/-- **The unshifted corank-`(r−1)` core value** `coreSchurGenVal r c'' Kr := ∫_{Δ∈matBox (r−1)(r−1) Kr}
∫_{S∈matBox (r−1) 4 Kr} frobSq(Δ·S)^{−c''}` — the `Sh`-independent finite constant the shifted residual is
bounded by (the carve-first assembly integrates the residual over the `rest`/shift coords, so it needs a
bound INDEPENDENT of `Sh`). Generic analog of `coreSchur2Val`. -/
noncomputable def coreSchurGenVal (r : ℕ) (c'' Kr : ℝ) : ℝ≥0∞ :=
  ∫⁻ Δ in matBox (r - 1) (r - 1) Kr, ∫⁻ S in matBox (r - 1) 4 Kr,
    ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))

/-- `coreSchurGenVal r c'' Kr < ⊤` for `0 < c'' < schurLambda (r−1)`, `0 < Kr`, `r ≥ 3` — via the abstract
lower IH at corank `r − 1`. -/
theorem coreSchurGenVal_lt_top (r : ℕ) (hr : 3 ≤ r) (hIH : SchurLowerIH 4 schurLambda r)
    (c'' : ℝ) (hc0 : 0 < c'') (hclam : c'' < schurLambda (r - 1)) (Kr : ℝ) (hKr : 0 < Kr) :
    coreSchurGenVal r c'' Kr < ⊤ := by
  have := hIH 1 (le_refl 1) (by omega) c'' hc0 (by simpa using hclam) Kr hKr
  rw [SchurCore] at this
  simpa [coreSchurGenVal] using this

/-- **The generic shifted-residual UNIFORM `_le` bound.** For a fixed shift `Sh` with `|Sh| ≤ B`, the
shifted corank-`(r−1)` core integral is `≤ coreSchurGenVal r c'' (K+B)` — a bound INDEPENDENT of `Sh` (only
the radius `K+B` records the shift size). Same chain as `schurResidG_translate_lt_top` (`Δ ↦ Δ − Sh`
translate into radius `K+B`), ending at the named value rather than `< ⊤`. The boundary-integrable form the
carve-first assembly consumes (mirror of `schurResid2_translate_le`). -/
theorem schurResidG_translate_le (r : ℕ) (hr : 3 ≤ r) (Sh : Fin (r - 1) → Fin (r - 1) → ℝ)
    (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B) (c'' : ℝ) (K : ℝ) :
    (∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) 4 K,
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
      ≤ coreSchurGenVal r c'' (K + B) := by
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
    rw [hg]
    refine lintegral_congr (fun S => ?_)
    rw [heqfun]
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
        * (flatBoxGen r T).indicator (gFlatGen r 4 c' T) (pivotBlowupOn
            (Finset.univ : Finset (Fin (r * r))) p y)
      = (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) (y p)
        * innerSGen r c' T p y := by
  by_cases hmem : pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) p y ∈ flatBoxGen r T
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
          * (flatBoxGen r T).indicator (gFlatGen r 4 c' T) (pivotBlowupOn
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
  rw [SchurCore, matBoxGen_outer_flat r 4 c' T,
    gFlatGen_cover_sum r 4 (by positivity) c' T]
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
