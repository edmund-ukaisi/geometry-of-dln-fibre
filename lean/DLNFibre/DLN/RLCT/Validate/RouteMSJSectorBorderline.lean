import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorBorderline
import DLNFibre.DLN.RLCT.Validate.RouteMSJTransversality

set_option linter.style.longLine false

/-!
# `RouteMSJSectorBorderline` — the j=0 SECTOR borderline over the `U_s` `m`-frame (hole (d), `hsector`)

**Thread `genm-sj5-hsecfix` (aoyagi-full Stage 2), the CORRECTED sector route.** The covervalid-addendum
sector routing was MIS-SCOPED: it keyed the two sub-cases off `M₂` (the deep-row dimension), but the
load-bearing invariant is the **effective deep rank** `ρ_Z = tailMinWidth = min(M₁,…,M_last)`, NOT `M₂`
(pen-and-paper `genm-dcoverhunt`, decorrelated-Codex-concurring, numerically confirmed). The corank weight
`∫ det((A_cor Z)(A_cor Z)ᵀ)^{−a/2}` is finite ⟺ `a+b ≤ ρ_Z` (codim `ρ_Z−b+1`), so the `M₂`-keyed
`uniformWenn_le` / `corankOffSector_borderline_le` are inapplicable (their full-`M₂`-rank hyps are
unsatisfiable whenever `M_last < M₂`).

This module lands, sorry-free, the CORRECT sector analytic core: a θ-interpolation BORDERLINE over the
`U_s` `m`-frame — the borderline analogue of `shell_corankOffSector_le_unif` (the convergent-regime `m`-frame
bound in `RouteMSJDeeperFlagCore`). At every hcvg-failing nonempty sector the over-run `(a+b) − m = 1`
EXACTLY (`m = tailMinWidth`), so the sector always sits at the `m`-frame LOG-borderline `a = m − b + 1`,
which the θ-interpolation closes for any `θ < 1` — the SAME mechanism as `corankOffSector_borderline_le`,
but keyed to the shell PSD floor `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)` instead of `Z.rank = M₂`.

## What lands here (all sorry-free)

* **`uniformWenn_proj_real_le`** — the strong-projection uniform corank weight at a REAL exponent `s ≥ 0`
  (the real-exponent analogue of `uniformWenn_proj_le`, needed because the borderline scales the `det`
  exponent by a real `θ`).
* **`shellCorankWeight_real_le_unif`** — the `Z`-uniform bound on the θ-scaled corank weight
  `∫ det((A·Z)(A·Z)ᵀ)^{−s/2} ≤ ε^{−sb}·(fixed-box weight)`, via the shell floor (m-frame), for real `s ≥ 0`.
* **`shell_corankOffSector_borderline_le_unif`** — the sector BORDERLINE bound: on the shell
  `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)`, for `θ ∈ [0,1)` with `θ·a < m − b + 1` (⟺ `θ < 1` at the border `a = m−b+1`),
  `∫_{A_cor}∫_Γ (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'} ≤ C₁ · w^{−(c'−θab/2)}` with `C₁ < ⊤` free of
  `w`. The `m`-frame analogue of `corankOffSector_borderline_le`.

## The structural facts the sector routing rests on (both general `∀L∀M`, NOT decide-checks)

* **`tailMinWidth_le_min_head_last`** — `tailMinWidth M ≤ min (M₁) (M_last)` UNCONDITIONALLY (the `m`-frame
  is never below the effective deep rank; the "`m ≥ tailMinWidth` always" leg of structural fact (1)).
* **`min_head_last_eq_tailMinWidth_of_nonempty`** — structural fact (1): at a nonempty sector
  (`min(M₁,M_last) ≤ tailMinWidth M`, the shell-0 nonemptiness) `min(M₁,M_last) = tailMinWidth M`.
* **`bindingCut_corank_add_le_tailMinWidth_succ`** — structural fact (2): the sharp sector bound
  `(M₀−t★) + (M₁−t★) ≤ tailMinWidth M + 1` at the binding cut `t★` (the correctly-keyed analogue of
  covervalid's `≤ M₂+1`).

S2-FREE. Intended axiom footprint `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

/-! ## The strong-projection uniform corank weight at a REAL exponent -/

/-- **The strong-projection uniform corank weight, real exponent `s ≥ 0`.** The real-exponent analogue of
`uniformWenn_proj_le`: on the shell `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)` (`U_sᵀ U_s = 1`, `U_s : M₂×m`, `b ≤ m`), the
corank weight is bounded UNIFORMLY by `ε^{−sb}` times the reduced weight over `A·U_s`,

    ∫_{A ∈ box(b×M₂)} det((A Z)(A Z)ᵀ)^{−s/2}
      ≤ ε^{−sb} · ∫_{A ∈ box(b×M₂)} det((A U_s)(A U_s)ᵀ)^{−s/2}.

Proof is `uniformWenn_proj_le` verbatim with the nat exponent `a'` replaced by a real `s ≥ 0` (only the
`ε`-power collapse `((ε²)^b)^{−s/2} = ε^{−sb}` and the exponent-sign `−s/2 ≤ 0` use `s`; the PSD
det-monotonicity is exponent-agnostic). Needed because the borderline scales the `det` exponent by a real
`θ`. -/
theorem uniformWenn_proj_real_le {b M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b ≤ m)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ A in matBox b M₂ 1,
        ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-s / 2)))
      ≤ ENNReal.ofReal (ε ^ (-(s * (b : ℝ))))
        * ∫⁻ A in matBox b M₂ 1,
            ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-s / 2)) := by
  classical
  have hmeasbox : MeasurableSet (matBox b M₂ 1) := matBox_measurableSet b M₂ 1
  have hεpow : ((ε ^ 2) ^ b : ℝ) ^ (-s / 2) = ε ^ (-(s * (b : ℝ))) := by
    rw [← pow_mul, ← Real.rpow_natCast ε (2 * b), ← Real.rpow_mul hε.le]
    congr 1; push_cast; ring
  -- `U_s` has rank `m ≥ b` (left inverse `U_sᵀ U_s = 1`).
  have hUsrank : b ≤ U_s.rank := by
    have h1 : (1 : Matrix (Fin m) (Fin m) ℝ).rank = m := by rw [Matrix.rank_one, Fintype.card_fin]
    have h2 : (U_sᵀ * U_s).rank ≤ U_s.rank := Matrix.rank_mul_le_right _ _
    rw [hUs, h1] at h2
    omega
  have hae := corank_survival_ae U_s hUsrank
  have hpt : ∀ A : Fin b → Fin M₂ → ℝ, (Matrix.of A * U_s).rank = b →
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-s / 2))
        ≤ ENNReal.ofReal (ε ^ (-(s * (b : ℝ))))
          * ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-s / 2)) := by
    intro A hrank
    have hADpd : ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).PosDef :=
      posDef_gram_of_rank_eq (Matrix.of A * U_s) hrank
    have hqpos : 0 < ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det :=
      lt_of_le_of_ne hADpd.posSemidef.det_nonneg
        (Ne.symm ((Matrix.isUnit_iff_isUnit_det _).mp hADpd.isUnit).ne_zero)
    have hgram : (Matrix.of A * Z) * (Matrix.of A * Z)ᵀ
        = Matrix.of A * (Z * Zᵀ) * (Matrix.of A)ᵀ := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    have hAUs : Matrix.of A * (U_s * U_sᵀ) * (Matrix.of A)ᵀ
        = (Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    have e1 : Matrix.of A * ((ε ^ 2) • (U_s * U_sᵀ)) * (Matrix.of A)ᵀ
        = (ε ^ 2) • ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, hAUs]
    have heq : Matrix.of A * (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)) * (Matrix.of A)ᵀ
        = (Matrix.of A * Z) * (Matrix.of A * Z)ᵀ
            - (ε ^ 2) • ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, e1, ← hgram]
    have hPSD_diff : ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ
        - (ε ^ 2) • ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ)).PosSemidef := by
      have h := hshell.mul_mul_conjTranspose_same (Matrix.of A)
      rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
      rwa [heq] at h
    have hN_psd : ((ε ^ 2) • ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ)).PosSemidef :=
      (posSemidef_mul_transpose (Matrix.of A * U_s)).smul (by positivity : (0 : ℝ) ≤ ε ^ 2)
    have hdetle : ((ε ^ 2) • ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ)).det
        ≤ ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det :=
      det_le_det_of_posSemidef_sub hN_psd hPSD_diff
    have hNdet : ((ε ^ 2) • ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ)).det
        = (ε ^ 2) ^ b * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det := by
      rw [Matrix.det_smul, Fintype.card_fin]
    rw [hNdet] at hdetle
    have hlow_pos : 0 < (ε ^ 2) ^ b * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det :=
      mul_pos (by positivity) hqpos
    have hexp_nonpos : -s / 2 ≤ 0 := by linarith
    have hrpow : ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-s / 2)
        ≤ ((ε ^ 2) ^ b * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det) ^ (-s / 2) :=
      Real.rpow_le_rpow_of_nonpos hlow_pos hdetle hexp_nonpos
    have hsplit : ((ε ^ 2) ^ b * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det) ^ (-s / 2)
        = ε ^ (-(s * (b : ℝ)))
          * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-s / 2) := by
      rw [Real.mul_rpow (by positivity) hqpos.le, hεpow]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ε ^ (-(s * (b : ℝ))))]
    apply ENNReal.ofReal_le_ofReal
    rw [hsplit] at hrpow
    exact hrpow
  calc ∫⁻ A in matBox b M₂ 1,
          ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-s / 2))
      ≤ ∫⁻ A in matBox b M₂ 1,
          ENNReal.ofReal (ε ^ (-(s * (b : ℝ))))
            * ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-s / 2)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
        filter_upwards [hae] with A hrank _hAbox
        exact hpt A hrank
    _ = ENNReal.ofReal (ε ^ (-(s * (b : ℝ))))
          * ∫⁻ A in matBox b M₂ 1,
              ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-s / 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The `Z`-uniform θ-scaled corank weight bound (m-frame, real exponent).** Composing
`uniformWenn_proj_real_le` (`Z → U_s`, factor `ε^{−sb}`) with `strongBlock_lintegral_le_unif`
(`U_s →` fixed box), the θ-scaled corank weight is bounded, `Z`-uniformly, by `ε^{−sb}` times the
fixed-box strong-block weight. The bounding fixed-box weight is finite for `s < m − b + 1`
(`strongBlock_unif_const_lt_top`), which is what makes the borderline `Wθ` finite for `θ < 1`. -/
theorem shellCorankWeight_real_le_unif {b M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b ≤ m) (hmM : m ≤ M₂)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ A in matBox b M₂ 1,
        ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-s / 2)))
      ≤ ENNReal.ofReal (ε ^ (-(s * (b : ℝ))))
        * ∫⁻ X in matBox b M₂ ((M₂ : ℝ) ^ 2),
            ENNReal.ofReal
              ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
                  * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-s / 2)) :=
  le_trans (uniformWenn_proj_real_le Z U_s hUs hbm hε hshell hs)
    (mul_le_mul_left' (strongBlock_lintegral_le_unif hmM U_s hUs) _)

/-! ## The sector borderline θ-interpolation bound over the `U_s` `m`-frame -/

/-- **The sector borderline θ-interpolation bound over the `U_s` `m`-frame.** The BORDERLINE analogue of
`shell_corankOffSector_le_unif` (the convergent `m`-frame bound). On the shell `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)`
(`U_sᵀ U_s = 1`, `b ≤ m ≤ M₂`, `m ≤ Z.rank`), a fixed pivot energy `w > 0`, cross-shift `Ccross`, `c'`
above the block Morse threshold `ab/2`, an interpolation weight `θ ∈ [0,1)` with the θ-scaled weight
integrable (`θ·a < m − b + 1`), and a finite-measure freed-corner domain `sΓ`, the corank-block integral
is bounded by a finite, `w`-independent constant times the θ-reduced power of `w`:

    ∫_{A_cor} [∫_{Γ∈sΓ} (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'}] dA_cor  ≤  C₁ · w^{−(c'−θ·ab/2)}.

At the sector borderline `a = m − b + 1` the convergent (`θ=1`) `m`-frame weight `∫ det^{−a/2}`
log-diverges, but `θ·a < m − b + 1 ⟺ θ < 1`, so any `θ < 1` gives a log-free bound. The two banked
pointwise bounds — the atom (`corankBlock_morsePeel_setLE`, core `≥ w`) and the bounded brick
(`corankBlock_boundedGen_le`) — bound the inner integral on the a.e. full-row-rank set;
`enn_geom_interp` takes their geometric mean (`borderline_real_identity` collapses the powers), and the
θ-scaled corank weight is finite via the `m`-frame `shellCorankWeight_real_le_unif` +
`strongBlock_unif_const_lt_top` (NOT the `M₂`-keyed `corankWeight_bpos_lt_top`, whose full-`M₂`-rank
hypothesis fails for `deepRank < M₂` chains). -/
theorem shell_corankOffSector_borderline_le_unif {a b M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b ≤ m) (hmM : m ≤ M₂)
    (hmZ : m ≤ Z.rank) {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef)
    (Ccross : Matrix (Fin a) (Fin n) ℝ) (c' θ : ℝ) (hc' : (a * b : ℝ) / 2 < c')
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hθa : θ * (a : ℝ) < (m : ℝ) - b + 1)
    (sΓ : Set (Fin a → Fin b → ℝ)) (hsΓ : volume sΓ < ⊤) (w : ℝ) (hw : 0 < w) :
    ∃ C₁ : ℝ≥0∞, C₁ < ⊤ ∧
      ∫⁻ A_cor in matBox b M₂ 1,
          ∫⁻ Γ in sΓ, ENNReal.ofReal
            ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c'))
        ≤ C₁ * ENNReal.ofReal (w ^ (-(c' - θ * (a * b : ℝ) / 2))) := by
  classical
  have hc0 : (0 : ℝ) ≤ c' := le_of_lt (lt_of_le_of_lt (by positivity) hc')
  have h1θ : (0 : ℝ) ≤ 1 - θ := by linarith
  -- the inner freed-corner integral as a function of the corank block `A_cor`
  set F : (Fin b → Fin M₂ → ℝ) → ℝ≥0∞ := fun A =>
    ∫⁻ Γ in sΓ, ENNReal.ofReal
      ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) with hFdef
  -- the θ-scaled corank weight (finite: `θ·a < m − b + 1`, via the m-frame shell floor)
  set Wθ : ℝ≥0∞ := ∫⁻ A in matBox b M₂ 1,
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(θ * (a : ℝ)) / 2)) with hWdef
  have hsa : (0 : ℝ) ≤ θ * (a : ℝ) := mul_nonneg hθ0 (Nat.cast_nonneg a)
  have hWfin : Wθ < ⊤ := by
    refine lt_of_le_of_lt (shellCorankWeight_real_le_unif Z U_s hUs hbm hmM hε hshell hsa) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (strongBlock_unif_const_lt_top hmM hbm hθa)
  -- the `A_cor`-independent constant (the Cresid factor + the bounded brick's volume)
  set Kconst : ℝ≥0∞ :=
      ENNReal.ofReal (Cresid (a * b) c' ^ θ * w ^ (-(c' - θ * (a * b : ℝ) / 2)))
        * (volume sΓ) ^ (1 - θ) with hKdef
  have hKfin : Kconst < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_lt_top_of_nonneg h1θ (ne_of_lt hsΓ))
  refine ⟨Wθ * ENNReal.ofReal (Cresid (a * b) c' ^ θ) * (volume sΓ) ^ (1 - θ), ?_, ?_⟩
  · -- finiteness of `C₁`
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hWfin ENNReal.ofReal_lt_top) ?_
    exact ENNReal.rpow_lt_top_of_nonneg h1θ (ne_of_lt hsΓ)
  -- the main bound
  have hmeasbox : MeasurableSet (matBox b M₂ 1) := matBox_measurableSet b M₂ 1
  have hbZ : b ≤ Z.rank := le_trans hbm hmZ
  have hfz : frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) = 0 := by simp [frobSq]
  -- the shifted core (`≥ w`, exponent `≤ 0`) is dominated by `w^{−(c'−ab/2)}`
  have hcorepow : ∀ X : Matrix (Fin a) (Fin n) ℝ,
      (w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) + frobSq X) ^ (-(c' - (a * b : ℝ) / 2))
        ≤ w ^ (-(c' - (a * b : ℝ) / 2)) := fun X =>
    Real.rpow_le_rpow_of_nonpos hw
      (by rw [hfz, add_zero]; exact le_add_of_nonneg_right (frobSq_nonneg _))
      (by linarith [hc'])
  -- the two banked pointwise bounds on the full-row-rank set + their geometric interpolation
  have hpt : ∀ A : Fin b → Fin M₂ → ℝ, (Matrix.of A * Z).rank = b →
      F A ≤ ENNReal.ofReal
              (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(θ * (a : ℝ)) / 2)) * Kconst := by
    intro A hrank
    have hPD := posDef_gram_of_rank_eq (Matrix.of A * Z) hrank
    have hatom := corankBlock_morsePeel_setLE (Apiv := (0 : Matrix (Fin 0) (Fin n) ℝ))
      (Ccross := Ccross) (Qb := Matrix.of A * Z) hPD c' hc' w hw sΓ
    set d : ℝ := ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det with hddef
    have hd0 : 0 ≤ d := by rw [hddef]; exact (posSemidef_mul_transpose _).det_nonneg
    have hFeq : F A = ∫⁻ Γ in sΓ, ENNReal.ofReal
        ((w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ)
          + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) := by
      simp only [hFdef]
      exact lintegral_congr (fun Γ => by rw [hfz, add_zero])
    -- ATOM (core dropped to `w`)
    have hAtomBound : F A ≤ ENNReal.ofReal
        (d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))) := by
      rw [hFeq]
      refine le_trans hatom ?_
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
            = d ^ (-(a : ℝ) / 2) * Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)) from by ring]
      exact mul_le_mul_of_nonneg_left (hcorepow _)
        (mul_nonneg (Real.rpow_nonneg hd0 _) (Cresid_nonneg _ _))
    -- BOUNDED brick
    have hBddBound : F A ≤ ENNReal.ofReal (w ^ (-c')) * volume sΓ := by
      simp only [hFdef]
      exact corankBlock_boundedGen_le Ccross (Matrix.of A * Z) c' hc0 w hw sΓ
    -- geometric interpolation, then collapse the `ℝ≥0∞`/`ℝ` powers
    refine (enn_geom_interp hθ0 hθ1.le hAtomBound hBddBound).trans (le_of_eq ?_)
    have hBatom_nn : (0 : ℝ)
        ≤ d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))) :=
      mul_nonneg (Real.rpow_nonneg hd0 _)
        (mul_nonneg (Cresid_nonneg _ _) (Real.rpow_nonneg hw.le _))
    calc (ENNReal.ofReal (d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))))) ^ θ
            * (ENNReal.ofReal (w ^ (-c')) * volume sΓ) ^ (1 - θ)
        = ENNReal.ofReal
              ((d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))) ^ θ)
            * (ENNReal.ofReal ((w ^ (-c')) ^ (1 - θ)) * (volume sΓ) ^ (1 - θ)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hBatom_nn hθ0, ENNReal.mul_rpow_of_nonneg _ _ h1θ,
              ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hw.le _) h1θ]
      _ = ENNReal.ofReal
              ((d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))) ^ θ
                * (w ^ (-c')) ^ (1 - θ)) * (volume sΓ) ^ (1 - θ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hBatom_nn _)]
      _ = ENNReal.ofReal
              (d ^ (-(θ * (a : ℝ)) / 2)
                * (Cresid (a * b) c' ^ θ * w ^ (-(c' - θ * (a * b : ℝ) / 2)))) * (volume sΓ) ^ (1 - θ) := by
          rw [borderline_real_identity hd0 hw (Cresid_nonneg _ _) a b]
      _ = ENNReal.ofReal (d ^ (-(θ * (a : ℝ)) / 2))
              * (ENNReal.ofReal (Cresid (a * b) c' ^ θ * w ^ (-(c' - θ * (a * b : ℝ) / 2)))
                  * (volume sΓ) ^ (1 - θ)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hd0 _), mul_assoc]
      _ = ENNReal.ofReal (d ^ (-(θ * (a : ℝ)) / 2)) * Kconst := by rw [← hKdef]
  -- integrate the a.e. pointwise bound, pull out `Kconst`, recognise `Wθ`
  calc ∫⁻ A in matBox b M₂ 1, F A
      ≤ ∫⁻ A in matBox b M₂ 1, ENNReal.ofReal
            (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(θ * (a : ℝ)) / 2)) * Kconst := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
        filter_upwards [corank_survival_ae Z hbZ] with A hrank _hAbox
        exact hpt A hrank
    _ = (∫⁻ A in matBox b M₂ 1, ENNReal.ofReal
            (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(θ * (a : ℝ)) / 2))) * Kconst :=
        lintegral_mul_const' Kconst _ (ne_of_lt hKfin)
    _ = Wθ * Kconst := by rw [← hWdef]
    _ = Wθ * ENNReal.ofReal (Cresid (a * b) c' ^ θ) * (volume sΓ) ^ (1 - θ)
          * ENNReal.ofReal (w ^ (-(c' - θ * (a * b : ℝ) / 2))) := by
        rw [hKdef, ENNReal.ofReal_mul (Real.rpow_nonneg (Cresid_nonneg _ _) _)]
        ring

/-! ## Structural fact (1) — the `m`-frame equals `tailMinWidth` at a nonempty sector -/

variable {L : ℕ}

/-- **Structural fact (1), the automatic leg.** `tailMinWidth M ≤ min (M 1) (M_last)` UNCONDITIONALLY:
`tailMinWidth` is the min over ALL tail widths `{M₁,…,M_last}`, so it is `≤` the min over the two-element
subset `{M₁, M_last}`. This is the "`m ≥ tailMinWidth` always" leg of the m-frame invariant (`m =
min(M₁,M_last)`). -/
theorem tailMinWidth_le_min_head_last (M : Fin (L + 1 + 1 + 1) → ℕ) :
    tailMinWidth M ≤ min (M 1) (M (Fin.last (L + 1 + 1))) := by
  rw [tailMinWidth]
  refine le_min ?_ ?_
  · refine le_trans (Finset.inf'_le _ (Finset.mem_univ (0 : Fin (L + 1 + 1)))) ?_
    rw [Fin.succ_zero_eq_one]
  · refine le_trans (Finset.inf'_le _ (Finset.mem_univ (Fin.last (L + 1)))) ?_
    rw [Fin.succ_last]

/-- **Structural fact (1).** At a nonempty sector — the shell-0 nonemptiness condition
`min (M 1) (M_last) ≤ tailMinWidth M` — the `m`-frame equals `tailMinWidth`:
`min (M 1) (M_last) = tailMinWidth M`. Antisymmetry of the automatic `tailMinWidth ≤ min` leg
(`tailMinWidth_le_min_head_last`) with the nonemptiness hypothesis. (The nonemptiness leg is geometric —
shell-`j` is empty for `j < min(M₁,M_last) − tailMinWidth`, so a nonempty shell-0 forces
`min(M₁,M_last) ≤ tailMinWidth`; supplied at wiring by the frame/emptiness routing, correcting the
covervalid `m ≤ M₂` filter to the sharp `m ≤ tailMinWidth`.) -/
theorem min_head_last_eq_tailMinWidth_of_nonempty (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hne : min (M 1) (M (Fin.last (L + 1 + 1))) ≤ tailMinWidth M) :
    min (M 1) (M (Fin.last (L + 1 + 1))) = tailMinWidth M :=
  le_antisymm hne (tailMinWidth_le_min_head_last M)

/-! ## Structural fact (2) — the sharp binding-cut corank bound `a★+b★ ≤ tailMinWidth+1` -/

/-- `minAdm` of a two-width leaf chain is the product of its widths. -/
theorem minAdm_two (N : Fin 2 → ℕ) : minAdm N = N 0 * N 1 := by
  rw [← minAdmRec_eq_minAdm N, minAdmRec_leaf]

/-- **The reduced chain of a prepended chain drops the prepended head.** For `redChain t` applied to a
chain with a prepended pivot `Fin.cons u tail`, the reduced chain replaces `(u, tail 0)` by the single
pivot `t`, keeping the deeper tail — i.e. `Fin.cons t (Fin.tail tail)`. (The reduced tail is INDEPENDENT
of the prepended head `u`, the fact the increment recursion turns on.) -/
theorem redChain_cons_tail {L : ℕ} (u t : ℕ) (tail : Fin (L + 1 + 1) → ℕ) :
    redChain t (Fin.cons u tail) = Fin.cons t (Fin.tail tail) := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> simp [Fin.tail]

/-- `minAdm` of a prepended-pivot two-width leaf `(a, tail 0)` is `a · tail 0`. -/
theorem minAdm_cons_singleton (a : ℕ) (tail : Fin 1 → ℕ) :
    minAdm (Fin.cons a tail) = a * tail 0 :=
  minAdm_two _

/-- **The conditional increment helper (the sharp key to fact (2)).** For a fixed deep tail `tail`, a
pivot width `u ≥ 1` and any budget `w`: IF the pivot-`u` reduced-chain value is within `u·w`
(`minAdm (Fin.cons u tail) ≤ u·w`), THEN raising the pivot to `u+1` costs at most `w`:

    minAdm (Fin.cons (u+1) tail) ≤ minAdm (Fin.cons u tail) + w.

Proof by induction on the tail arity (Codex-designed, decorrelated). Let `c = tail 0` and let `s` attain
the pivot-`u` peel-min, `q = c − s`. If `q ≤ w`, reuse `s` at `u+1` (cost `q ≤ w`). If `q > w`, then
`s ≥ 1` (else `minAdm = u·c = u·q > u·w`), and `q ≥ w` forces the deeper value `V'(s) ≤ s·w`, so the IH
applies at `s`; using `s+1` as the `u+1` competitor the deeper `+w` is offset by the `−(u−s)` block
saving. This is the sharp `tailMinWidth`-keyed bound (NOT the loose `M₂` one): only the SINGLE budget
hypothesis at `u` is needed. -/
theorem minAdm_cons_succ_le_of_le : {L : ℕ} → (tail : Fin (L + 1) → ℕ) → (u w : ℕ) → 1 ≤ u →
    minAdm (Fin.cons u tail) ≤ u * w →
    minAdm (Fin.cons (u + 1) tail) ≤ minAdm (Fin.cons u tail) + w
  | 0, tail, u, w, hu, hle => by
      -- leaf: minAdm (u, c) = u·c; `hle` gives `c ≤ w`.
      rw [minAdm_cons_singleton u tail] at hle
      rw [minAdm_cons_singleton u tail, minAdm_cons_singleton (u + 1) tail]
      have hcw : tail 0 ≤ w := Nat.le_of_mul_le_mul_left hle hu
      have hring : (u + 1) * tail 0 = u * tail 0 + tail 0 := by ring
      omega
  | (L + 1), tail, u, w, hu, hle => by
      classical
      -- head values of the two chains
      have hce : (Fin.cons u tail : Fin (L + 1 + 1 + 1) → ℕ) 1 = tail 0 := by
        rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
      have hN10 : (Fin.cons (u + 1) tail : Fin (L + 1 + 1 + 1) → ℕ) 0 = u + 1 := Fin.cons_zero _ _
      have hN11 : (Fin.cons (u + 1) tail : Fin (L + 1 + 1 + 1) → ℕ) 1 = tail 0 := by
        rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
      -- competitor bound at cut `s'` for the pivot-`(u+1)` chain.
      have hcomp : ∀ s', s' ≤ min (u + 1) (tail 0) →
          minAdm (Fin.cons (u + 1) tail)
            ≤ (u + 1 - s') * (tail 0 - s') + minAdm (Fin.cons s' (Fin.tail tail)) := by
        intro s' hs'
        have hs'min : s' ≤ min ((Fin.cons (u + 1) tail : Fin (L + 1 + 1 + 1) → ℕ) 0)
            ((Fin.cons (u + 1) tail : Fin (L + 1 + 1 + 1) → ℕ) 1) := by rw [hN10, hN11]; exact hs'
        have h := minAdm_le_peelCharge_add_redChain (Fin.cons (u + 1) tail) s' hs'min
        rwa [peelCharge, hN10, hN11, redChain_cons_tail (u + 1) s' tail] at h
      -- the minimizer `s` of the pivot-`u` peel (binding cut).
      obtain ⟨s, hsle0, hseq⟩ := exists_binding_cut (Fin.cons u tail)
      rw [Fin.cons_zero, hce] at hsle0
      have hVal : minAdm (Fin.cons u tail)
          = (u - s) * (tail 0 - s) + minAdm (Fin.cons s (Fin.tail tail)) := by
        rw [hseq, peelCharge, Fin.cons_zero, hce, redChain_cons_tail u s tail]
      by_cases hqw : tail 0 - s ≤ w
      · -- q ≤ w: reuse `s`.
        have hb := hcomp s (by omega)
        have hexp : (u + 1 - s) * (tail 0 - s) = (u - s) * (tail 0 - s) + (tail 0 - s) := by
          have h1 : u + 1 - s = (u - s) + 1 := by omega
          rw [h1]; ring
        rw [hexp] at hb
        rw [hVal]; omega
      · -- q > w.
        push_neg at hqw
        -- `s ≥ 1`.
        have hs1 : 1 ≤ s := by
          rcases Nat.eq_zero_or_pos s with hs0 | hs0
          · exfalso
            have hle' := hle
            rw [hVal, hs0] at hle'
            simp only [Nat.sub_zero] at hle'
            have huc : u * tail 0 ≤ u * w := by omega
            have hcw : tail 0 ≤ w := Nat.le_of_mul_le_mul_left huc hu
            omega
          · exact hs0
        -- `minAdm (cons s (Fin.tail tail)) ≤ s * w`.
        have hVsle : minAdm (Fin.cons s (Fin.tail tail)) ≤ s * w := by
          have hle' := hle
          rw [hVal] at hle'
          have hqge : w ≤ tail 0 - s := le_of_lt hqw
          have h1 : (u - s) * w ≤ (u - s) * (tail 0 - s) := by gcongr
          have h2 : (u - s) * w + s * w = u * w := by
            rw [← add_mul]; congr 1; omega
          omega
        -- IH at `s` (tail arity `L`).
        have hIH := minAdm_cons_succ_le_of_le (Fin.tail tail) s w hs1 hVsle
        -- competitor `s+1` for the pivot-`(u+1)` chain.
        have hb := hcomp (s + 1) (by omega)
        have hexp : (u + 1 - (s + 1)) * (tail 0 - (s + 1)) + (u - s) = (u - s) * (tail 0 - s) := by
          have e1 : u + 1 - (s + 1) = u - s := by omega
          have e2 : tail 0 - (s + 1) + 1 = tail 0 - s := by omega
          rw [e1, ← e2]; ring
        rw [hVal]; omega

/-- **Structural fact (2) — the sharp binding-cut corank bound.** At a NONDEGENERATE binding cut `t★`
of `M` (`a★ = M₀−t★ ≥ 1`, `b★ = M₁−t★ ≥ 1`, from `t★+1 ≤ min(M₀,M₁)`) with `t★ ≥ 1`, under the goodness
gate `hpiv : minAdm (redChain t★ M) ≤ t★·tailMinWidth M`, the binding-cut corank widths sum to at most
`tailMinWidth M + 1`:

    (M₀ − t★) + (M₁ − t★) ≤ tailMinWidth M + 1.

This is the correctly-keyed analogue of the covervalid addendum's `a★+b★ ≤ M₂+1` (`tailMinWidth ≤ M₂`,
so this is SHARPER). Combines the LOWER convexity `minAdm_redChain_succ_ge` (banked; the reduced-chain
value jumps by `≥ a★+b★−1`) with the UPPER conditional increment `minAdm_cons_succ_le_of_le` (the jump is
`≤ tailMinWidth` under `hpiv`); the two pinch `a★+b★−1 ≤ tailMinWidth`. Only `hpiv` at `t★` is needed
(NOT full `∀u` goodness); the LEAST-achiever property of the binding cut is unused — only that it achieves
the peel-min (`hbind`). -/
theorem bindingCut_corank_add_le_tailMinWidth_succ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht1 : 1 ≤ t) (hnext : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (hpiv : minAdm (redChain t M) ≤ t * tailMinWidth M) :
    (M 0 - t) + (M 1 - t) ≤ tailMinWidth M + 1 := by
  -- UPPER increment via the conditional helper (tail = deep widths `M₂,…,M_last`).
  have hincr : minAdm (redChain (t + 1) M) ≤ minAdm (redChain t M) + tailMinWidth M :=
    minAdm_cons_succ_le_of_le (fun i => M i.succ.succ) t (tailMinWidth M) ht1 hpiv
  -- LOWER convexity (banked): the reduced value jumps by `≥ a★+b★−1`.
  have hconv := minAdm_redChain_succ_ge M t hnext hbind
  have ha : 1 ≤ M 0 - t := by omega
  have hb : 1 ≤ M 1 - t := by omega
  omega

/-- **Structural fact (2), at the canonical binding cut.** The `bindingCut M`-specialisation: at
`t★ = bindingCut M` (a `≥ 3`-width chain) with `t★ ≥ 1`, `t★+1 ≤ min(M₀,M₁)`, and the goodness gate
`hpiv`, `(M₀−t★)+(M₁−t★) ≤ tailMinWidth M + 1`. The binding identity is read off `bindingCut`'s defining
`Nat.find` spec, so only the genuineness + goodness hypotheses remain. -/
theorem bindingCut_corank_add_le_tailMinWidth_succ' {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ)
    (ht1 : 1 ≤ bindingCut M) (hnext : bindingCut M + 1 ≤ min (M 0) (M 1))
    (hpiv : minAdm (redChain (bindingCut M) M) ≤ bindingCut M * tailMinWidth M) :
    (M 0 - bindingCut M) + (M 1 - bindingCut M) ≤ tailMinWidth M + 1 := by
  have hbind : minAdm M = peelCharge M (bindingCut M) + minAdm (redChain (bindingCut M) M) :=
    (Nat.find_spec (exists_binding_cut M)).2
  exact bindingCut_corank_add_le_tailMinWidth_succ M (bindingCut M) ht1 hnext hbind hpiv

end DLNFibre.DLN.RLCT
