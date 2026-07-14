import DLNFibre.DLN.RLCT.Validate.RouteMSJShellUniform
import DLNFibre.DLN.RLCT.Validate.RouteMSJShellCover
import DLNFibre.DLN.RLCT.Validate.RouteMSJGramRowPeel

set_option linter.style.longLine false

/-!
# `RouteMSJDeeperFlagShell` — the off-sector-over-`Z` shell stratification (T-Obl3b mountain, tile #3)

**Thread `genm-sj5-domination`, T-Obl3b mountain, build tile #3 — CORRECTED route (chart cert
`tobl3b-cornershift-chart-cert.md`, 2026-07-13).** The re-formulation §6 bordered-Gram corner-shrink
primitive was REFUTED (its Jacobian is a divergent non-sequitur); the corrected corner-shrink is a
**deeper-cut (`t★+j`) re-peel + banked PSD-monotonicity** — NO bordered-Gram, NO minor Jacobian. This
file holds the DLN-closure pieces for that corrected route.

## What lands here (sorry-free)

* **`detGram_eq_prod_rows`** — the concrete product form `det(X Xᵀ) = ∏ᵢ gramSchurSeq (rowsEquiv X) i`
  (consumes banked `gram_rowsEquiv` + `gramDet_eq_prod`). This is the bordered-Gram DIAGNOSTIC identity
  — correct and reusable, but NOT the corner-shrink mechanism (chart cert §6).
* **`offSector_cover_le`** — the mountain's cover assembly over the single-`ε` exhaustive shell cover,
  `∫ over box, f ≤ ∑ⱼ ∫ over singularShell ε r j, f`. Measurability-free.
* **`uniformWenn_proj_le`** (OWED-1) — `uniformWenn_le` generalised from the identity `1` to a strong
  projection `P := U_s U_sᵀ` (`U_sᵀ U_s = 1`): on the shell where `Z Zᵀ ⪰ ε²·P`, the corank weight is
  bounded UNIFORMLY (factor `ε^{−a'b'}`, weak-SV-free) by the reduced weight over `A·U_s`. The banked
  PSD-monotonicity weak-direction elimination `M₂ → m` at the reduced corank width `b'` and exponent
  `a'`. This is the corrected corner-shrink's Step 2 (chart cert §1, §5 OWED-1). NO bordered-Gram.

## Held (OWED-2/OWED-3)

* **OWED-2 `strongBlock_lintegral_lt_top`** — the strictly-convergent reduced weight at the shrunk dims
  `(b−j, M₂−j, a−j)`, via an orthogonal extension of `U_s` + measure-preserving right-multiplication +
  `detGram_lintegral_lt_top`. Being built next.
* **OWED-3 `deeperFlag_shell_le`** — the mountain assembly. Its LHS is the cut-`u = t★+j` integrand
  produced by the T-peel spine peeling per shell (NOT the divergent cut-`t★` integrand of reformulation
  §3), held for the decorrelated T-peel-spine wall-check (agent a5cc889); assembled from Step-1 corner
  peel → OWED-1 → OWED-2 → `cornerComparator` + `flagShift_lt_carrierThreshold`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

/-- **The concrete product-of-Schur-residuals form of `det(X Xᵀ)`.** Combining the banked Gram identity
`gram_rowsEquiv` with the abstract product factorisation `gramDet_eq_prod`. (Diagnostic identity — not
the corner-shrink primitive; see chart cert §6.) -/
theorem detGram_eq_prod_rows {r n : ℕ} (X : Fin r → Fin n → ℝ)
    (hli : LinearIndependent ℝ (rowsEquiv r n X)) :
    (Matrix.of X * (Matrix.of X)ᵀ).det = ∏ i, gramSchurSeq (rowsEquiv r n X) i := by
  rw [← gram_rowsEquiv X]
  exact gramDet_eq_prod (rowsEquiv r n X) hli

/-- **The single-`ε` shell-cover assembly for the mountain.** For any nonnegative integrand `f` over
the deep-product space and any base region `box`, the integral over `box` is bounded by the sum over
the exhaustive count-shell cover. Measurability-free (only exhaustiveness is used). -/
theorem offSector_cover_le {M₂ nn : ℕ} (μ : Measure (Fin M₂ → Fin nn → ℝ))
    (ε : ℝ) (r : ℕ) (f : (Fin M₂ → Fin nn → ℝ) → ℝ≥0∞)
    (box : Set (Fin M₂ → Fin nn → ℝ)) :
    ∫⁻ Z in box, f Z ∂μ
      ≤ ∑ j : Fin (r + 1), ∫⁻ Z in (singularShell ε r j : Set (Fin M₂ → Fin nn → ℝ)), f Z ∂μ := by
  refine lintegral_le_sum_finCover (fun j => (singularShell ε r j : Set (Fin M₂ → Fin nn → ℝ))) f ?_
  rw [show (⋃ j, (singularShell ε r j : Set (Fin M₂ → Fin nn → ℝ))) = Set.univ from
    singularShell_iUnion ε r]
  exact Set.subset_univ box

/-- **OWED-1 — the strong-projection uniform corank weight.** `uniformWenn_le` generalised from the
identity `1` to a strong projection `P := U_s U_sᵀ` with `U_sᵀ U_s = 1` (`U_s : M₂×m`, `b' ≤ m`). On
the shell `Z Zᵀ ⪰ ε²·P`, the corank weight is bounded UNIFORMLY by `ε^{−a'b'}` times the reduced weight
over `A·U_s`:

    ∫_{A ∈ box(b'×M₂)} det((A Z)(A Z)ᵀ)^{−a'/2}
      ≤ ε^{−a'b'} · ∫_{A ∈ box(b'×M₂)} det((A U_s)(A U_s)ᵀ)^{−a'/2}.

This is the corrected corner-shrink Step 2 (chart cert §1, §5 OWED-1) — banked PSD-monotonicity
weak-direction elimination `M₂ → m`, NO bordered-Gram, NO minor Jacobian. Proof is `uniformWenn_le`
verbatim with `1 → U_s U_sᵀ` (the congruence `A·(ε²•P)·Aᵀ = ε²•((A U_s)(A U_s)ᵀ)`; `det_smul` gives
`(ε²)^{b'}`; `U_s` has rank `m ≥ b'` from `U_sᵀ U_s = 1`). -/
theorem uniformWenn_proj_le {a' b' M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b' ≤ m)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef) :
    (∫⁻ A in matBox b' M₂ 1,
        ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a' : ℝ) / 2)))
      ≤ ENNReal.ofReal (ε ^ (-((a' : ℝ) * b')))
        * ∫⁻ A in matBox b' M₂ 1,
            ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-(a' : ℝ) / 2)) := by
  classical
  have hmeasbox : MeasurableSet (matBox b' M₂ 1) := matBox_measurableSet b' M₂ 1
  have hεpow : ((ε ^ 2) ^ b' : ℝ) ^ (-(a' : ℝ) / 2) = ε ^ (-((a' : ℝ) * b')) := by
    rw [← pow_mul, ← Real.rpow_natCast ε (2 * b'), ← Real.rpow_mul hε.le]
    congr 1; push_cast; ring
  -- `U_s` has rank `m ≥ b'` (left inverse `U_sᵀ U_s = 1`)
  have hUsrank : b' ≤ U_s.rank := by
    have h1 : (1 : Matrix (Fin m) (Fin m) ℝ).rank = m := by rw [Matrix.rank_one, Fintype.card_fin]
    have h2 : (U_sᵀ * U_s).rank ≤ U_s.rank := Matrix.rank_mul_le_right _ _
    rw [hUs, h1] at h2
    omega
  have hae := corank_survival_ae U_s hUsrank
  have hpt : ∀ A : Fin b' → Fin M₂ → ℝ, (Matrix.of A * U_s).rank = b' →
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a' : ℝ) / 2))
        ≤ ENNReal.ofReal (ε ^ (-((a' : ℝ) * b')))
          * ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-(a' : ℝ) / 2)) := by
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
        = (ε ^ 2) ^ b' * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det := by
      rw [Matrix.det_smul, Fintype.card_fin]
    rw [hNdet] at hdetle
    have hlow_pos : 0 < (ε ^ 2) ^ b' * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det :=
      mul_pos (by positivity) hqpos
    have hexp_nonpos : -(a' : ℝ) / 2 ≤ 0 := by
      have : (0 : ℝ) ≤ (a' : ℝ) := Nat.cast_nonneg a'; linarith
    have hrpow : ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a' : ℝ) / 2)
        ≤ ((ε ^ 2) ^ b' * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det) ^ (-(a' : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hlow_pos hdetle hexp_nonpos
    have hsplit : ((ε ^ 2) ^ b' * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det) ^ (-(a' : ℝ) / 2)
        = ε ^ (-((a' : ℝ) * b'))
          * ((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-(a' : ℝ) / 2) := by
      rw [Real.mul_rpow (by positivity) hqpos.le, hεpow]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ε ^ (-((a' : ℝ) * b')))]
    apply ENNReal.ofReal_le_ofReal
    rw [hsplit] at hrpow
    exact hrpow
  calc ∫⁻ A in matBox b' M₂ 1,
          ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a' : ℝ) / 2))
      ≤ ∫⁻ A in matBox b' M₂ 1,
          ENNReal.ofReal (ε ^ (-((a' : ℝ) * b')))
            * ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-(a' : ℝ) / 2)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
        filter_upwards [hae] with A hrank _hAbox
        exact hpt A hrank
    _ = ENNReal.ofReal (ε ^ (-((a' : ℝ) * b')))
          * ∫⁻ A in matBox b' M₂ 1,
              ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-(a' : ℝ) / 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end DLNFibre.DLN.RLCT
