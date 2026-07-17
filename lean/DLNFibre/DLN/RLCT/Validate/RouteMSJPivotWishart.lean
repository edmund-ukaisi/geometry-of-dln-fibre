import DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorBPos
import DLNFibre.DLN.RLCT.Validate.RouteMSJDetMono
import DLNFibre.DLN.RLCT.Validate.RouteMSJGramSqrt

set_option linter.style.longLine false

/-!
# `RouteMSJPivotWishart` — the pivot top-stratum Gram disposal (Lane 2, obligation 1)

**Thread `genm-l2pivot`, aoyagi-full endgame.** The TOP-STRATUM pivot-Gram disposal — obligation 1 of
`RouteMSJProductCorankEngine.corankStratum_lt_top` (l2engine), transcription of the l2svd certificate
§8 route (`svd-chart-design.md`). SCOPE: the top stratum only (the `a < b − t + 1` gate); the deeper
rank-drop strata are obligation 2 (`nonsubmersive_Ar_principalization`, the HELD wall) — NOT here.

## What obligation 1 delivers

After the coupling `C` is integrated out (`gammaAtom_aniso_shifted_eq`, banked), the freed integrand
carries the **PIVOT Gram** `det(Qtₚ·Qtₚᵀ)^{−a/2}` where `Qtₚ = Q_p + P⁻¹·B₁₂·Q_b` is the pivot-shifted
tail (`t × q`; `Q_b` `b × q` full row rank on the top stratum, `Q_p` `t × q`). Certificate §8 step 1
(`B₁₂ ↦ B' := P⁻¹·B₁₂`, a linear CoV with bounded Jacobian `|det P|^b`) frees the pivot to
`Qtₚ = Q_p + B'·Q_b`. This file discharges the resulting **free-`B'`** integral

    ∫_{B' ∈ box} det((Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ)^{−a/2}  < ⊤   (gate `a < b − t + 1`),

which is the mathematical content of obligation 1. The outer `P`-integral is a bounded-factor wrapper
(`|det P|^b` bounded on the `P`-box, `|det Ψ|^{−t}` a constant) that l2engine adds when wiring.

## The route (l2svd cert §8), all banked pieces named

The free-ification is a projection compress of `Q_b` onto its own row space:

* **`pivotGram_compress`** — via the Gram normaliser `exists_gram_normalizer` on `Q_b·Q_bᵀ` PosDef,
  set `M := (Q_b·Q_bᵀ)^{−1/2}`, `col := Q_bᵀ·M` (orthonormal columns), `P := col·colᵀ` (the orthogonal
  projection onto the row space of `Q_b`). There is an invertible `Ψ := Q_b·col` (`b × b`,
  `= (Q_b·Q_bᵀ)^{1/2}`), a shift `R₁ := Q_p·col` (`t × b`) and a PSD residual
  `C₀ := (Q_p·(1−P))·(Q_p·(1−P))ᵀ` (`t × t`) with
      `det((Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ) = det((R₁ + B'·Ψ)·(R₁ + B'·Ψ)ᵀ + C₀)`   for all `B'`.
  This is a pure ALGEBRAIC integrand rewrite (`Q_b·P = Q_b` + `col·colᵀ + (1−P) = 1`), NOT a measure
  CoV — and it needs no orthogonal extension / column split.
* **`affineShiftGram_box_lt_top`** — the free-Wishart endpoint: `∫ det((R₁ + B'·Ψ)(…)ᵀ + C₀)^{−a/2}`
  is finite for a PSD shift `C₀`, via the affine CoV `B' ↦ R₁ + B'·Ψ` (`lintegral_comp_rightMulₚ` +
  translation `lintegral_add_right_eq_self`), the Löwner PSD-shift domination
  `det(Y·Yᵀ + C₀) ≥ det(Y·Yᵀ)` (`det_le_det_of_posSemidef_sub`, banked P1), the a.e. full-rank fact
  (`corank_survival_ae`, banked), and the banked free-Wishart integral `detGram_lintegral_box_lt_top`
  at gate `a < b − t + 1`.

## The DEAD routes honored (recon §DEAD)

Carry the PIVOT Gram `det(Qtₚ·Qtₚᵀ)`, NEVER the corank Gram `det(Q_b·Q_bᵀ)` (atom trap). The PSD shift
`C₀` only HELPS (`det(·+C₀) ≥ det(·)`); the Jacobian `|det Ψ|^{−t}` is carried, never dropped.

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

/-- **The pivot-tail compress.** For `Q_b` (`b × q`) of full row rank (`Q_b·Q_bᵀ` PosDef) and any
`Q_p` (`t × q`), there is an invertible `Ψ` (`b × b`), a shift `R₁` (`t × b`) and a PSD residual `C₀`
(`t × t`) with, for every `B'` (`t × b`),

    det((Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ) = det((R₁ + B'·Ψ)·(R₁ + B'·Ψ)ᵀ + C₀).

Let `M := (Q_b·Q_bᵀ)^{−1/2}` (Gram normaliser), `col := Q_bᵀ·M` (orthonormal columns `colᵀ·col = 1`),
and `P := col·colᵀ` (the orthogonal projection onto the row space of `Q_b`, symmetric and idempotent).
Take `Ψ := Q_b·col` (`= (Q_b·Q_bᵀ)^{1/2}`, invertible), `R₁ := Q_p·col`,
`C₀ := (Q_p·(1−P))·(Q_p·(1−P))ᵀ`. Since `Q_b·P = Q_b` (the rows of `Q_b` sit in the projection's range),
`Q_b·(1−P) = 0`, so the shift `Q_p·(1−P)·Q_pᵀ` sees only `Q_p`, and `col·colᵀ + (1−P) = 1` reassembles
`(Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ` — no orthogonal extension / column split needed. -/
theorem pivotGram_compress {t b q : ℕ}
    (Qp : Matrix (Fin t) (Fin q) ℝ) (Qb : Matrix (Fin b) (Fin q) ℝ)
    (hQb : (Qb * Qbᵀ).PosDef) :
    ∃ (Ψ : Matrix (Fin b) (Fin b) ℝ) (R₁ : Matrix (Fin t) (Fin b) ℝ)
      (C₀ : Matrix (Fin t) (Fin t) ℝ),
      Ψ.det ≠ 0 ∧ C₀.PosSemidef ∧
      ∀ B' : Fin t → Fin b → ℝ,
        ((Qp + Matrix.of B' * Qb) * (Qp + Matrix.of B' * Qb)ᵀ).det
          = ((R₁ + Matrix.of B' * Ψ) * (R₁ + Matrix.of B' * Ψ)ᵀ + C₀).det := by
  classical
  obtain ⟨M, hMsymm, hMGM, hMdet, _⟩ := exists_gram_normalizer (Qb * Qbᵀ) hQb
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hMdet
  -- `M * (Qb Qbᵀ) * M = 1` (symmetric normaliser).
  have hMGM' : M * (Qb * Qbᵀ) * M = 1 := by rw [hMsymm] at hMGM; exact hMGM
  set col : Matrix (Fin q) (Fin b) ℝ := Qbᵀ * M with hcoldef
  have hcolT : colᵀ = M * Qb := by
    rw [hcoldef, Matrix.transpose_mul, Matrix.transpose_transpose, hMsymm]
  -- `colᵀ * col = 1` (orthonormal columns).
  have hcolortho : colᵀ * col = 1 := by
    rw [hcolT, hcoldef, Matrix.mul_assoc, ← Matrix.mul_assoc Qb, ← Matrix.mul_assoc M, hMGM']
  set P : Matrix (Fin q) (Fin q) ℝ := col * colᵀ with hPdef
  have hPsymm : Pᵀ = P := by rw [hPdef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPidem : P * P = P := by
    rw [hPdef, Matrix.mul_assoc, ← Matrix.mul_assoc colᵀ, hcolortho, Matrix.one_mul]
  -- `G * M * M = 1`, hence `Qb * P = Qb`.
  have hMGM'' : M * ((Qb * Qbᵀ) * M) = 1 := by rw [← Matrix.mul_assoc]; exact hMGM'
  have hGM_rinv : M⁻¹ = (Qb * Qbᵀ) * M := Matrix.inv_eq_right_inv hMGM''
  have hGMM : (Qb * Qbᵀ) * M * M = 1 := by rw [← hGM_rinv, Matrix.nonsing_inv_mul M hMunit]
  have hQbP : Qb * P = Qb := by
    rw [hPdef, hcolT, hcoldef]
    calc Qb * (Qbᵀ * M * (M * Qb))
        = (Qb * Qbᵀ) * M * M * Qb := by
          simp only [Matrix.mul_assoc]
      _ = Qb := by rw [hGMM, Matrix.one_mul]
  set Ψ : Matrix (Fin b) (Fin b) ℝ := Qb * col with hΨdef
  set R₁ : Matrix (Fin t) (Fin b) ℝ := Qp * col with hR₁def
  set C₀ : Matrix (Fin t) (Fin t) ℝ := (Qp * (1 - P)) * (Qp * (1 - P))ᵀ with hC₀def
  refine ⟨Ψ, R₁, C₀, ?_, posSemidef_mul_transpose _, ?_⟩
  · -- `det Ψ ≠ 0`
    have hΨeq : Ψ = (Qb * Qbᵀ) * M := by rw [hΨdef, hcoldef, Matrix.mul_assoc]
    rw [hΨeq, Matrix.det_mul]
    exact mul_ne_zero (ne_of_gt hQb.det_pos) hMdet
  · -- the matrix identity (via `congrArg det`)
    intro B'
    refine congrArg Matrix.det ?_
    set B : Matrix (Fin t) (Fin b) ℝ := Matrix.of B' with hBdef
    set Qt : Matrix (Fin t) (Fin q) ℝ := Qp + B * Qb with hQtdef
    -- `1 - P` symmetric idempotent; `Qb (1-P) = 0` and `(1-P) Qbᵀ = 0`.
    have hsymm1P : (1 - P)ᵀ = 1 - P := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, hPsymm]
    have hidem1P : (1 - P) * (1 - P) = 1 - P := by
      have h : (1 - P) * (1 - P) = 1 - P - P + P * P := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]; abel
      rw [h, hPidem]; abel
    have hQb1P : Qb * (1 - P) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hQbP, sub_self]
    have h1PQbT : (1 - P) * Qbᵀ = 0 := by
      have h := congrArg Matrix.transpose hQb1P
      rwa [Matrix.transpose_mul, hsymm1P, Matrix.transpose_zero] at h
    -- `R₁ + B Ψ = Qt col`.
    have hkey1 : R₁ + B * Ψ = Qt * col := by
      rw [hR₁def, hΨdef, hQtdef, Matrix.add_mul, Matrix.mul_assoc B Qb col]
    -- `(Qt col)(Qt col)ᵀ = Qt P Qtᵀ`.
    have hkey2 : (Qt * col) * (Qt * col)ᵀ = Qt * P * Qtᵀ := by
      rw [hPdef, Matrix.transpose_mul, ← Matrix.mul_assoc (Qt * col) colᵀ Qtᵀ,
        Matrix.mul_assoc Qt col colᵀ]
    -- `C₀ = Qt (1-P) Qtᵀ` (both sides `= Qp (1-P) Qpᵀ`).
    have hCa : C₀ = Qp * (1 - P) * Qpᵀ := by
      rw [hC₀def, Matrix.transpose_mul, hsymm1P,
        ← Matrix.mul_assoc (Qp * (1 - P)) (1 - P) Qpᵀ, Matrix.mul_assoc Qp (1 - P) (1 - P),
        hidem1P]
    have hleft : Qt * (1 - P) = Qp * (1 - P) := by
      rw [hQtdef, Matrix.add_mul, Matrix.mul_assoc B Qb (1 - P), hQb1P, Matrix.mul_zero, add_zero]
    have hCb : Qt * (1 - P) * Qtᵀ = Qp * (1 - P) * Qpᵀ := by
      rw [hQtdef, Matrix.transpose_add, Matrix.transpose_mul, ← hQtdef, hleft,
        Matrix.mul_add, Matrix.mul_assoc Qp (1 - P) (Qbᵀ * Bᵀ),
        ← Matrix.mul_assoc (1 - P) Qbᵀ Bᵀ, h1PQbT, Matrix.zero_mul, Matrix.mul_zero, add_zero]
    have hkey3 : C₀ = Qt * (1 - P) * Qtᵀ := hCa.trans hCb.symm
    -- assemble: `Qt Qtᵀ = Qt P Qtᵀ + Qt (1-P) Qtᵀ`.
    have hsplit : Qt * Qtᵀ = Qt * P * Qtᵀ + Qt * (1 - P) * Qtᵀ := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, show P + (1 - P) = 1 from by abel, Matrix.mul_one]
    rw [hkey1, hkey2, hkey3]; exact hsplit

/-! ## Obligation 1 — the free-`B'` pivot-Gram disposal -/

/-- **Obligation 1 (top stratum): the free-`B'` pivot-Gram disposal.** For `Q_b` (`b × q`) of full row
rank (`Q_b·Q_bᵀ` PosDef, `b ≤ q`), any `Q_p` (`t × q`), and the convergent regime `a < b − t + 1`
(`0 ≤ a`), the free-`B'` pivot-Gram integral is finite:

    ∫_{B' ∈ matBox t b 1} det((Q_p + B'·Q_b)·(Q_p + B'·Q_b)ᵀ)^{−a/2}   < ⊤.

Combine the compress (`pivotGram_compress`) with the affine endpoint (`affineShiftGram_box_lt_top`,
`C₀ := R₂·R₂ᵀ` PSD). This is the mathematical content of obligation 1 (l2svd cert §8); the outer
`P`-integral is a bounded-factor wrapper l2engine adds when wiring. -/
theorem pivotGram_freeShift_lt_top {t b q : ℕ}
    (Qp : Matrix (Fin t) (Fin q) ℝ) (Qb : Matrix (Fin b) (Fin q) ℝ)
    (hQb : (Qb * Qbᵀ).PosDef)
    {a : ℝ} (ha : 0 ≤ a) (hgate : a < (b : ℝ) - t + 1) :
    (∫⁻ B' in matBox t b 1,
        ENNReal.ofReal
          (((Qp + Matrix.of B' * Qb) * (Qp + Matrix.of B' * Qb)ᵀ).det ^ (-a / 2))) < ⊤ := by
  obtain ⟨Ψ, R₁, C₀, hΨ, hC₀, hcompress⟩ := pivotGram_compress Qp Qb hQb
  calc (∫⁻ B' in matBox t b 1,
          ENNReal.ofReal
            (((Qp + Matrix.of B' * Qb) * (Qp + Matrix.of B' * Qb)ᵀ).det ^ (-a / 2)))
      = ∫⁻ B' in matBox t b 1,
          ENNReal.ofReal
            (((R₁ + Matrix.of B' * Ψ) * (R₁ + Matrix.of B' * Ψ)ᵀ + C₀).det ^ (-a / 2)) := by
        refine setLIntegral_congr_fun (matBox_measurableSet t b 1) (fun B' _ => ?_)
        rw [hcompress B']
    _ < ⊤ := affineShiftGram_box_lt_top ha hgate R₁ Ψ hΨ C₀ hC₀

end DLNFibre.DLN.RLCT
