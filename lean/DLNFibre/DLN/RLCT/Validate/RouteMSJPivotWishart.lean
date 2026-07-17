import DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorBPos
import DLNFibre.DLN.RLCT.Validate.RouteMSJDetMono
import DLNFibre.DLN.RLCT.Validate.RouteMSJOrthoExtend
import DLNFibre.DLN.RLCT.Validate.RouteMSJGramSqrt
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# `RouteMSJPivotWishart` — the pivot top-stratum Gram disposal (Lane 2, obligation 1)

**Thread `genm-l2pivot`, aoyagi-full endgame.** The TOP-STRATUM pivot-Gram disposal — obligation 1 of
`RouteMSJProductCorankEngine.corankStratum_lt_top` (l2engine), transcription of the l2svd certificate
§8 route (`svd-chart-design.md`). SCOPE: the top stratum only (the `a < b − t + 1` gate); the deeper
rank-drop strata are obligation 2 (`nonsubmersive_Ar_principalization`, the HELD wall) — NOT here.

## What obligation 1 delivers

After the coupling `C` is integrated out (`gammaAtom_aniso_shifted_eq`, banked), the freed integrand
carries the **PIVOT Gram** `det(Q̃ₚ·Q̃ₚᵀ)^{−a/2}` where `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b` is the pivot-shifted
tail (`t × q`; `Q_b` `b × q` full row rank on the top stratum, `Q_p` `t × q`). Certificate §8 step 1
(`B₁₂ ↦ B' := P⁻¹·B₁₂`, a linear CoV with bounded Jacobian `|det P|^b`) frees the pivot to
`Q̃ₚ = Q_p + B'·Q_b`. This file discharges the resulting **free-`B'`** integral

    ∫_{B' ∈ box} det((Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ)^{−a/2}  < ⊤   (gate `a < b − t + 1`),

which is the mathematical content of obligation 1. The outer `P`-integral is a bounded-factor wrapper
(`|det P|^b` bounded on the `P`-box, `|det Ψ|^{−t}` a constant) that l2engine adds when wiring.

## The route (l2svd cert §8), all banked pieces named

The free-ification is a right-orthogonal compress of `Q_b`:

* **`pivotGram_compress`** — pick the right-singular frame of `Q_b` (via the Gram normaliser
  `exists_gram_normalizer` on `Q_b·Q_bᵀ` PosDef + the orthogonal extension `exists_ortho_ext`): there is
  an invertible `Ψ` (`b × b`, `= (Q_b·Q_bᵀ)^{1/2}`), a shift `R₁` (`t × b`) and a residual `R₂`
  (`t × (q−b)`) with
      `det((Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ) = det((R₁ + B'·Ψ)·(R₁ + B'·Ψ)ᵀ + R₂·R₂ᵀ)`   for all `B'`.
  The compress is an ALGEBRAIC integrand rewrite (Gram-invariance under the orthogonal `V`,
  `V·Vᵀ = 1`), NOT a measure CoV.
* **`affineShiftGram_box_lt_top`** — the free-Wishart endpoint: `∫ det((R₁ + B'·Ψ)(…)ᵀ + C₀)^{−a/2}`
  is finite for a PSD shift `C₀`, via the affine CoV `B' ↦ R₁ + B'·Ψ` (`lintegral_comp_rightMulₚ` +
  translation), the Löwner PSD-shift domination `det(Y·Yᵀ + C₀) ≥ det(Y·Yᵀ)`
  (`det_le_det_of_posSemidef_sub`, banked P1), the a.e. full-rank fact (`corank_survival_ae`, banked),
  and the banked free-Wishart integral `detGram_lintegral_box_lt_top` at gate `a < b − t + 1`.

## The DEAD routes honored (recon §DEAD)

Carry the PIVOT Gram `det(Q̃ₚ·Q̃ₚᵀ)`, NEVER the corank Gram `det(Q_b·Q_bᵀ)` (atom trap). The PSD shift
`C₀ = R₂·R₂ᵀ` only HELPS (`det(·+C₀) ≥ det(·)`); the Jacobian `|det Ψ|^{−t}` is carried, never dropped.

UNTRACKED / NOT wired into `DLNFibre.lean` or `AxCheck` — l2engine merges + wires it. Intended axiom
footprint `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## The affine free-Wishart endpoint (cert §8 steps 3–4) -/

/-- **The affine PSD-shifted free-Wishart integral is finite (top stratum).** For an invertible right
factor `Ψ` (`b × b`), an affine shift `R₁` (`t × b`), and a PSD shift `C₀` (`t × t`), in the convergent
regime `a < b − t + 1` (`0 ≤ a`), the box integral

    ∫_{B' ∈ matBox t b 1} det((R₁ + B'·Ψ)·(R₁ + B'·Ψ)ᵀ + C₀)^{−a/2}   < ⊤.

Route: affine CoV `B' ↦ R₁ + B'·Ψ` (right-mult `lintegral_comp_rightMulₚ` + translation), the Löwner
PSD-shift domination (`det_le_det_of_posSemidef_sub`, the shift only helps), the a.e. full-row-rank fact
(`corank_survival_ae`), and the banked free-Wishart box integral `detGram_lintegral_box_lt_top`. -/
theorem affineShiftGram_box_lt_top {t b : ℕ}
    {a : ℝ} (ha : 0 ≤ a) (hgate : a < (b : ℝ) - t + 1)
    (R₁ : Matrix (Fin t) (Fin b) ℝ) (Ψ : Matrix (Fin b) (Fin b) ℝ) (hΨ : Ψ.det ≠ 0)
    (C₀ : Matrix (Fin t) (Fin t) ℝ) (hC₀ : C₀.PosSemidef) :
    (∫⁻ B' in matBox t b 1,
        ENNReal.ofReal
          (((R₁ + Matrix.of B' * Ψ) * (R₁ + Matrix.of B' * Ψ)ᵀ + C₀).det ^ (-a / 2))) < ⊤ := by
  classical
  -- `t ≤ b` follows from the gate `0 ≤ a < b − t + 1`.
  have htb : t ≤ b := by
    by_contra h
    push_neg at h
    have hbt : (b : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith
  -- The `(R₁, C₀)`-shifted integrand as a function of the post-right-mult variable `Y'`.
  set f : (Fin t → Fin b → ℝ) → ℝ≥0∞ :=
    fun Y' => ENNReal.ofReal
      (((R₁ + Matrix.of Y') * (R₁ + Matrix.of Y')ᵀ + C₀).det ^ (-a / 2)) with hfdef
  have hfmeas : Measurable f := by
    have hcont : Continuous (fun Y' : Fin t → Fin b → ℝ =>
        ((R₁ + Matrix.of Y') * (R₁ + Matrix.of Y')ᵀ + C₀).det) := by
      apply Continuous.matrix_det
      refine continuous_matrix (fun i j => ?_)
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
      refine Continuous.add (continuous_finset_sum _ (fun k _ => Continuous.mul ?_ ?_))
        continuous_const
      · exact Continuous.add continuous_const ((continuous_apply k).comp (continuous_apply i))
      · exact Continuous.add continuous_const ((continuous_apply k).comp (continuous_apply j))
    exact ENNReal.measurable_ofReal.comp
      (((by fun_prop : Measurable (fun x : ℝ => x ^ (-a / 2)))).comp hcont.measurable)
  -- `Matrix.of (fun i ↦ B' i ᵥ* Ψ) = Matrix.of B' * Ψ`.
  have hof : ∀ B' : Fin t → Fin b → ℝ, Matrix.of (fun i => B' i ᵥ* Ψ) = Matrix.of B' * Ψ := by
    intro B'; ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  -- the integrand rewrite `goal B' = f (fun i ↦ B' i ᵥ* Ψ)`.
  have hint : ∀ B' : Fin t → Fin b → ℝ,
      ENNReal.ofReal
          (((R₁ + Matrix.of B' * Ψ) * (R₁ + Matrix.of B' * Ψ)ᵀ + C₀).det ^ (-a / 2))
        = f (fun i => B' i ᵥ* Ψ) := by
    intro B'; rw [hfdef]; simp only [hof B']
  -- unit facts for `Ψ`.
  have hΨunit : IsUnit Ψ.det := (isUnit_iff_ne_zero).mpr hΨ
  have hΨinvdet : (Ψ⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hΨ
  -- the preimage box `s` and its enclosure into `matBox t b T₁`.
  set s : Set (Fin t → Fin b → ℝ) := {Y' | (fun i => Y' i ᵥ* Ψ⁻¹) ∈ matBox t b 1} with hsdef
  have hmapmeas : Measurable (fun Y' : Fin t → Fin b → ℝ => (fun i => Y' i ᵥ* Ψ⁻¹)) := by
    refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.measurable_sum _ (fun k _ =>
      (((measurable_pi_apply k).comp (measurable_pi_apply i)).mul measurable_const))
  have hsmeas : MeasurableSet s := hmapmeas (matBox_measurableSet t b 1)
  have hfun : ∀ B' : Fin t → Fin b → ℝ, (fun i => (B' i ᵥ* Ψ) ᵥ* Ψ⁻¹) = B' := by
    intro B'; funext i
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv Ψ hΨunit, Matrix.vecMul_one]
  have hmem : ∀ B' : Fin t → Fin b → ℝ, (fun i => B' i ᵥ* Ψ) ∈ s ↔ B' ∈ matBox t b 1 := by
    intro B'; simp only [hsdef, Set.mem_setOf_eq, hfun B']
  set T₁ : ℝ := ∑ k : Fin b, ∑ j : Fin b, |Ψ k j| with hT₁def
  have hsub : s ⊆ matBox t b T₁ := by
    intro Y' hY'
    simp only [hsdef, Set.mem_setOf_eq, matBox, Set.mem_setOf_eq] at hY' ⊢
    intro i j
    rw [Set.mem_Icc]
    have hrec : (Y' i ᵥ* Ψ⁻¹) ᵥ* Ψ = Y' i := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul Ψ hΨunit, Matrix.vecMul_one]
    have hentry : Y' i j = ∑ k, (Y' i ᵥ* Ψ⁻¹) k * Ψ k j := by
      conv_lhs => rw [← hrec]
      simp only [Matrix.vecMul, dotProduct]
    have habs : |Y' i j| ≤ T₁ := by
      rw [hentry]
      calc |∑ k, (Y' i ᵥ* Ψ⁻¹) k * Ψ k j|
          ≤ ∑ k, |(Y' i ᵥ* Ψ⁻¹) k * Ψ k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, |Ψ k j| := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [abs_mul]
            have hmb := hY' i k
            rw [Set.mem_Icc] at hmb
            have h1 : |(Y' i ᵥ* Ψ⁻¹) k| ≤ 1 := abs_le.mpr hmb
            nlinarith [abs_nonneg (Ψ k j), h1]
        _ ≤ T₁ := by
            rw [hT₁def]
            exact Finset.sum_le_sum (fun k _ =>
              Finset.single_le_sum (f := fun j' => |Ψ k j'|)
                (fun j' _ => abs_nonneg _) (Finset.mem_univ j))
    exact abs_le.mp habs
  -- STEP 1: the right-mult change of variables `B' ↦ B' · Ψ`.
  rw [show (∫⁻ B' in matBox t b 1,
        ENNReal.ofReal
          (((R₁ + Matrix.of B' * Ψ) * (R₁ + Matrix.of B' * Ψ)ᵀ + C₀).det ^ (-a / 2)))
      = ∫⁻ B' in matBox t b 1, f (fun i => B' i ᵥ* Ψ) from lintegral_congr (fun B' => hint B')]
  rw [← lintegral_indicator (matBox_measurableSet t b 1)]
  rw [show (∫⁻ B', (matBox t b 1).indicator (fun B' => f (fun i => B' i ᵥ* Ψ)) B')
      = ∫⁻ B', (s.indicator f) (fun i => B' i ᵥ* Ψ) from lintegral_congr (fun B' => by
        by_cases hB' : B' ∈ matBox t b 1
        · rw [Set.indicator_of_mem hB', Set.indicator_of_mem ((hmem B').mpr hB')]
        · rw [Set.indicator_of_notMem hB',
            Set.indicator_of_notMem (fun h => hB' ((hmem B').mp h))])]
  rw [lintegral_comp_rightMulₚ t Ψ hΨ (s.indicator f) (hfmeas.indicator hsmeas),
    lintegral_indicator hsmeas]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  -- the translation shift `r₁` (`R₁` as a function), the shifted target `T₂`, and the free integrand `g`.
  set r₁ : Fin t → Fin b → ℝ := fun i j => R₁ i j with hr₁def
  set T₂ : ℝ := T₁ + ∑ i : Fin t, ∑ j : Fin b, |R₁ i j| with hT₂def
  set g : (Fin t → Fin b → ℝ) → ℝ≥0∞ :=
    fun Y'' => ENNReal.ofReal (((Matrix.of Y'') * (Matrix.of Y'')ᵀ + C₀).det ^ (-a / 2)) with hgdef
  have hfg : ∀ Y' : Fin t → Fin b → ℝ, f Y' = g (Y' + r₁) := by
    intro Y'
    have hmat : R₁ + Matrix.of Y' = Matrix.of (Y' + r₁) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply, hr₁def]
      ring
    simp only [hfdef, hgdef, hmat]
  have hb1 : t ≤ (1 : Matrix (Fin b) (Fin b) ℝ).rank := by
    rw [Matrix.rank_one, Fintype.card_fin]; exact htb
  -- STEP 2: enclose `s ⊆ matBox t b T₁`.
  calc ∫⁻ Y' in s, f Y' ≤ ∫⁻ Y' in matBox t b T₁, f Y' := lintegral_mono_set hsub
    -- STEP 3: translation `Y' ↦ Y' + R₁` absorbs the affine shift (into `matBox t b T₂`).
    _ = ∫⁻ Y' in matBox t b T₁, g (Y' + r₁) :=
        setLIntegral_congr_fun (matBox_measurableSet t b T₁) (fun Y' _ => hfg Y')
    _ ≤ ∫⁻ Y'' in matBox t b T₂, g Y'' := by
        rw [← lintegral_indicator (matBox_measurableSet t b T₁),
          ← lintegral_indicator (matBox_measurableSet t b T₂)]
        calc ∫⁻ Y', (matBox t b T₁).indicator (fun Y' => g (Y' + r₁)) Y'
            ≤ ∫⁻ Y', (matBox t b T₂).indicator g (Y' + r₁) := by
              refine lintegral_mono (fun Y' => ?_)
              by_cases hY' : Y' ∈ matBox t b T₁
              · have hmem2 : Y' + r₁ ∈ matBox t b T₂ := by
                  simp only [matBox, Set.mem_setOf_eq] at hY' ⊢
                  intro i j
                  rw [Set.mem_Icc]
                  have hY'ij := hY' i j
                  rw [Set.mem_Icc] at hY'ij
                  have hentryv : (Y' + r₁) i j = Y' i j + R₁ i j := by
                    simp only [Pi.add_apply, hr₁def]
                  have hbd : |Y' i j + R₁ i j| ≤ T₂ := by
                    calc |Y' i j + R₁ i j| ≤ |Y' i j| + |R₁ i j| := abs_add_le _ _
                      _ ≤ T₁ + ∑ i' : Fin t, ∑ j' : Fin b, |R₁ i' j'| := by
                          gcongr
                          · exact abs_le.mpr hY'ij
                          · exact (Finset.single_le_sum (f := fun j' => |R₁ i j'|)
                                (fun j' _ => abs_nonneg _) (Finset.mem_univ j)).trans
                              (Finset.single_le_sum (f := fun i' => ∑ j' : Fin b, |R₁ i' j'|)
                                (fun i' _ => Finset.sum_nonneg (fun j' _ => abs_nonneg _))
                                (Finset.mem_univ i))
                      _ = T₂ := by rw [hT₂def]
                  rw [hentryv]; exact abs_le.mp hbd
                exact (le_of_eq (Set.indicator_of_mem hY' (fun Y'' => g (Y'' + r₁)))).trans
                  (le_of_eq (Set.indicator_of_mem hmem2 g).symm)
              · rw [Set.indicator_of_notMem hY']; exact zero_le _
          _ = ∫⁻ Y'', (matBox t b T₂).indicator g Y'' :=
              lintegral_add_right_eq_self ((matBox t b T₂).indicator g) r₁
    -- STEP 4: Löwner PSD-shift domination `det(Y Yᵀ + C₀) ≥ det(Y Yᵀ)`, a.e. (rank-drop null).
    _ ≤ ∫⁻ Y'' in matBox t b T₂,
          ENNReal.ofReal (((Matrix.of Y'') * (Matrix.of Y'')ᵀ).det ^ (-a / 2)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' (matBox_measurableSet t b T₂)).mpr ?_)
        filter_upwards [corank_survival_ae (1 : Matrix (Fin b) (Fin b) ℝ) hb1] with Y'' hrank _
        have hrk : (Matrix.of Y'').rank = t := by rwa [Matrix.mul_one] at hrank
        have hPD : ((Matrix.of Y'') * (Matrix.of Y'')ᵀ).PosDef :=
          posDef_gram_of_rank_eq (Matrix.of Y'') hrk
        have hApos : 0 < ((Matrix.of Y'') * (Matrix.of Y'')ᵀ).det := hPD.det_pos
        have hdetle : ((Matrix.of Y'') * (Matrix.of Y'')ᵀ).det
            ≤ ((Matrix.of Y'') * (Matrix.of Y'')ᵀ + C₀).det := by
          refine det_le_det_of_posSemidef_sub hPD.posSemidef ?_
          rwa [add_sub_cancel_left]
        rw [hgdef]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_nonpos hApos hdetle (by linarith))
    -- STEP 5: the banked free-Wishart box integral.
    _ < ⊤ := detGram_lintegral_box_lt_top htb hgate T₂

/-! ## The right-orthogonal compress (cert §8 step 2, the free-ification) -/

/-- **The pivot-tail compress.** For `Q_b` (`b × q`) of full row rank (`Q_b·Q_bᵀ` PosDef, `b ≤ q`) and
any `Q_p` (`t × q`), there is an invertible `Ψ` (`b × b`), a shift `R₁` (`t × b`) and a residual `R₂`
(`t × (q−b)`) with, for every `B'` (`t × b`),

    det((Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ) = det((R₁ + B'·Ψ)·(R₁ + B'·Ψ)ᵀ + R₂·R₂ᵀ).

The right-singular frame `V` of `Q_b` (orthogonal, `Q_b·V = [Ψ | 0]`) rewrites the Gram by
orthogonal-invariance (`V·Vᵀ = 1`); the pivot's image splits into the `Ψ`-active block `R₁ + B'·Ψ` and
the constant residual `R₂`. -/
theorem pivotGram_compress {t b q : ℕ} (hbq : b ≤ q)
    (Qp : Matrix (Fin t) (Fin q) ℝ) (Qb : Matrix (Fin b) (Fin q) ℝ)
    (hQb : (Qb * Qbᵀ).PosDef) :
    ∃ (Ψ : Matrix (Fin b) (Fin b) ℝ) (R₁ : Matrix (Fin t) (Fin b) ℝ)
      (R₂ : Matrix (Fin t) (Fin (q - b)) ℝ),
      Ψ.det ≠ 0 ∧
      ∀ B' : Fin t → Fin b → ℝ,
        ((Qp + Matrix.of B' * Qb) * (Qp + Matrix.of B' * Qb)ᵀ).det
          = ((R₁ + Matrix.of B' * Ψ) * (R₁ + Matrix.of B' * Ψ)ᵀ + R₂ * R₂ᵀ).det := by
  sorry

/-! ## Obligation 1 — the free-`B'` pivot-Gram disposal -/

/-- **Obligation 1 (top stratum): the free-`B'` pivot-Gram disposal.** For `Q_b` (`b × q`) of full row
rank (`Q_b·Q_bᵀ` PosDef, `b ≤ q`), any `Q_p` (`t × q`), and the convergent regime `a < b − t + 1`
(`0 ≤ a`), the free-`B'` pivot-Gram integral is finite:

    ∫_{B' ∈ matBox t b 1} det((Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ)^{−a/2}   < ⊤.

Combine the compress (`pivotGram_compress`) with the affine endpoint (`affineShiftGram_box_lt_top`,
`C₀ := R₂·R₂ᵀ` PSD). This is the mathematical content of obligation 1 (l2svd cert §8); the outer
`P`-integral is a bounded-factor wrapper l2engine adds when wiring. -/
theorem pivotGram_freeShift_lt_top {t b q : ℕ} (hbq : b ≤ q)
    (Qp : Matrix (Fin t) (Fin q) ℝ) (Qb : Matrix (Fin b) (Fin q) ℝ)
    (hQb : (Qb * Qbᵀ).PosDef)
    {a : ℝ} (ha : 0 ≤ a) (hgate : a < (b : ℝ) - t + 1) :
    (∫⁻ B' in matBox t b 1,
        ENNReal.ofReal
          (((Qp + Matrix.of B' * Qb) * (Qp + Matrix.of B' * Qb)ᵀ).det ^ (-a / 2))) < ⊤ := by
  obtain ⟨Ψ, R₁, R₂, hΨ, hcompress⟩ := pivotGram_compress hbq Qp Qb hQb
  have hC₀ : (R₂ * R₂ᵀ).PosSemidef := posSemidef_mul_transpose R₂
  calc (∫⁻ B' in matBox t b 1,
          ENNReal.ofReal
            (((Qp + Matrix.of B' * Qb) * (Qp + Matrix.of B' * Qb)ᵀ).det ^ (-a / 2)))
      = ∫⁻ B' in matBox t b 1,
          ENNReal.ofReal
            (((R₁ + Matrix.of B' * Ψ) * (R₁ + Matrix.of B' * Ψ)ᵀ + R₂ * R₂ᵀ).det ^ (-a / 2)) := by
        refine setLIntegral_congr_fun (matBox_measurableSet t b 1) (fun B' _ => ?_)
        rw [hcompress B']
    _ < ⊤ := affineShiftGram_box_lt_top ha hgate R₁ Ψ hΨ (R₂ * R₂ᵀ) hC₀

end DLNFibre.DLN.RLCT
