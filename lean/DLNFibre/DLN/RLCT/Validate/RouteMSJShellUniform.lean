import DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorBPos
import DLNFibre.DLN.RLCT.Validate.RouteMSJDetMono
import DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJShellUniform` — T-Obl3a, the shell-0 uniform corank weight

**Thread `genm-sj5` off-sector, T-Obl3b build tile #1 (`final-assembly-design-cert.md` §5).** The
shell-0 (coercive-`Z`) leg of the Obl-3 singular-value-shell stratification: the LANDED per-fixed-`Z`
off-sector bound (`corankOffSector_bpos_le`) carries a `Z`-DEPENDENT constant `C₁(Z) = Cresid·Wenn(Z)`,
with the corank weight

    Wenn(Z) := ∫_{A ∈ matBox b M₂ 1} det((A·Z)(A·Z)ᵀ)^{−a/2}

blowing up as `σ_min(Z) → 0`. On the good shell `S₀ = {σ_min(Z) ≥ ε}` — Loewner-encoded as
`ZZᵀ ⪰ ε²·I` — this module upgrades the per-`Z` bound to a **`Z`-UNIFORM** one:

    Wenn(Z) ≤ ε^{−ab} · Wenn(I_{M₂}).

## The mechanism (design §1, Obl-3(a); decorrelated-Codex-confirmed "no additional uniformity hole")

Pointwise, for full-row-rank `A` (the a.e. set via `corank_survival_ae`):

* `(A·Z)(A·Z)ᵀ = A·(ZZᵀ)·Aᵀ`, and `ZZᵀ − ε²·I ⪰ 0` congruence-transports to
  `A·(ZZᵀ)·Aᵀ − ε²·(A·Aᵀ) = A·(ZZᵀ − ε²·I)·Aᵀ ⪰ 0` (`PosSemidef.mul_mul_conjTranspose_same`);
* so `A·(ZZᵀ)·Aᵀ ⪰ ε²·(A·Aᵀ)`, and PSD-determinant monotonicity (banked `det_le_det_of_posSemidef_sub`)
  gives `det((A·Z)(A·Z)ᵀ) ≥ (ε²)^b·det(A·Aᵀ) > 0`;
* the negative power `x ↦ x^{−a/2}` is antitone on `(0,∞)`, so
  `det((A·Z)(A·Z)ᵀ)^{−a/2} ≤ ((ε²)^b·det(A·Aᵀ))^{−a/2} = ε^{−ab}·det(A·Aᵀ)^{−a/2}`.

Integrate the a.e. pointwise bound (the rank-drop locus is null) and pull the `Z`-independent constant
`ε^{−ab}` out (`lintegral_const_mul'`). `Wenn(I_{M₂}) < ⊤` is the banked `detGram_lintegral_box_lt_top`
(`a < M₂ − b + 1`); the uniform factor `ε^{−ab}` is `Z`-free — the shell-0 constant is `Z`-uniform.

S2-FREE: banked det monotonicity + PSD congruence + a.e. corank survival; no `monomial_rlct`, no
`cited_aoyagi_dln`. Intended axiom footprint `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-- **T-Obl3a — the shell-0 uniform corank weight.** On the good shell `ZZᵀ ⪰ ε²·I` (all singular
values of `Z` bounded below by `ε > 0`), the corank weight `Wenn(Z)` is bounded UNIFORMLY (the factor
`ε^{−ab}` is `Z`-free) by `Wenn(I_{M₂})`:

    ∫_{A ∈ matBox b M₂ 1} det((A·Z)(A·Z)ᵀ)^{−a/2}
      ≤ ε^{−ab} · ∫_{A ∈ matBox b M₂ 1} det(A·Aᵀ)^{−a/2}.

`b ≤ M₂` is the corank-block hypothesis (holds at every binding cut). This is the `Z`-uniform
replacement for the `Z`-dependent `Wenn(Z)` of `corankOffSector_bpos_le` on the coercive shell. -/
theorem uniformWenn_le {a b M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ) (hbM : b ≤ M₂)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (1 : Matrix (Fin M₂) (Fin M₂) ℝ)).PosSemidef) :
    (∫⁻ A in matBox b M₂ 1,
        ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)))
      ≤ ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
        * ∫⁻ A in matBox b M₂ 1,
            ENNReal.ofReal (((Matrix.of A) * (Matrix.of A)ᵀ).det ^ (-(a : ℝ) / 2)) := by
  classical
  have hmeasbox : MeasurableSet (matBox b M₂ 1) := matBox_measurableSet b M₂ 1
  -- the uniform exponent identity `((ε²)^b)^{−a/2} = ε^{−ab}`
  have hεpow : ((ε ^ 2) ^ b : ℝ) ^ (-(a : ℝ) / 2) = ε ^ (-((a : ℝ) * b)) := by
    rw [← pow_mul, ← Real.rpow_natCast ε (2 * b), ← Real.rpow_mul hε.le]
    congr 1
    push_cast; ring
  -- the a.e. full-row-rank set (`Z := 1`, rank `M₂ ≥ b`)
  have hrank1 : b ≤ (1 : Matrix (Fin M₂) (Fin M₂) ℝ).rank := by
    rw [Matrix.rank_one, Fintype.card_fin]; exact hbM
  have hae := corank_survival_ae (1 : Matrix (Fin M₂) (Fin M₂) ℝ) hrank1
  -- the pointwise bound on the full-row-rank set
  have hpt : ∀ A : Fin b → Fin M₂ → ℝ, (Matrix.of A).rank = b →
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2))
        ≤ ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
          * ENNReal.ofReal (((Matrix.of A) * (Matrix.of A)ᵀ).det ^ (-(a : ℝ) / 2)) := by
    intro A hrank
    -- `A·Aᵀ` is PosDef, so its determinant is strictly positive
    have hADpd : ((Matrix.of A) * (Matrix.of A)ᵀ).PosDef := posDef_gram_of_rank_eq (Matrix.of A) hrank
    have hqpos : 0 < ((Matrix.of A) * (Matrix.of A)ᵀ).det :=
      lt_of_le_of_ne hADpd.posSemidef.det_nonneg
        (Ne.symm ((Matrix.isUnit_iff_isUnit_det _).mp hADpd.isUnit).ne_zero)
    -- `(A·Z)(A·Z)ᵀ = A·(ZZᵀ)·Aᵀ`
    have hgram : (Matrix.of A * Z) * (Matrix.of A * Z)ᵀ
        = Matrix.of A * (Z * Zᵀ) * (Matrix.of A)ᵀ := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    -- congruence: `A·(ZZᵀ − ε²·I)·Aᵀ = (A·Z)(A·Z)ᵀ − ε²·(A·Aᵀ)`
    have e1 : Matrix.of A * ((ε ^ 2) • (1 : Matrix (Fin M₂) (Fin M₂) ℝ)) * (Matrix.of A)ᵀ
        = (ε ^ 2) • ((Matrix.of A) * (Matrix.of A)ᵀ) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    have heq : Matrix.of A * (Z * Zᵀ - (ε ^ 2) • (1 : Matrix (Fin M₂) (Fin M₂) ℝ)) * (Matrix.of A)ᵀ
        = (Matrix.of A * Z) * (Matrix.of A * Z)ᵀ
            - (ε ^ 2) • ((Matrix.of A) * (Matrix.of A)ᵀ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, e1, ← hgram]
    -- the difference is PSD (Loewner congruence of the shell hypothesis)
    have hPSD_diff : ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ
        - (ε ^ 2) • ((Matrix.of A) * (Matrix.of A)ᵀ)).PosSemidef := by
      have h := hshell.mul_mul_conjTranspose_same (Matrix.of A)
      rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
      rwa [heq] at h
    -- the smaller matrix `ε²·(A·Aᵀ)` is PSD
    have hN_psd : ((ε ^ 2) • ((Matrix.of A) * (Matrix.of A)ᵀ)).PosSemidef :=
      (posSemidef_mul_transpose (Matrix.of A)).smul (by positivity : (0 : ℝ) ≤ ε ^ 2)
    -- PSD determinant monotonicity
    have hdetle : ((ε ^ 2) • ((Matrix.of A) * (Matrix.of A)ᵀ)).det
        ≤ ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det :=
      det_le_det_of_posSemidef_sub hN_psd hPSD_diff
    have hNdet : ((ε ^ 2) • ((Matrix.of A) * (Matrix.of A)ᵀ)).det
        = (ε ^ 2) ^ b * ((Matrix.of A) * (Matrix.of A)ᵀ).det := by
      rw [Matrix.det_smul, Fintype.card_fin]
    rw [hNdet] at hdetle
    -- the strictly-positive lower bound `(ε²)^b·det(A·Aᵀ)`
    have hlow_pos : 0 < (ε ^ 2) ^ b * ((Matrix.of A) * (Matrix.of A)ᵀ).det := by
      have : 0 < (ε ^ 2) ^ b := by positivity
      exact mul_pos this hqpos
    -- antitone negative power
    have hexp_nonpos : -(a : ℝ) / 2 ≤ 0 := by
      have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      linarith
    have hrpow : ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)
        ≤ ((ε ^ 2) ^ b * ((Matrix.of A) * (Matrix.of A)ᵀ).det) ^ (-(a : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hlow_pos hdetle hexp_nonpos
    -- split the product power and rewrite `((ε²)^b)^{−a/2} = ε^{−ab}`
    have hsplit : ((ε ^ 2) ^ b * ((Matrix.of A) * (Matrix.of A)ᵀ).det) ^ (-(a : ℝ) / 2)
        = ε ^ (-((a : ℝ) * b)) * ((Matrix.of A) * (Matrix.of A)ᵀ).det ^ (-(a : ℝ) / 2) := by
      rw [Real.mul_rpow (by positivity) hqpos.le, hεpow]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ε ^ (-((a : ℝ) * b)))]
    apply ENNReal.ofReal_le_ofReal
    rw [hsplit] at hrpow
    exact hrpow
  -- integrate the a.e. bound and pull out the `Z`-uniform constant
  calc ∫⁻ A in matBox b M₂ 1,
          ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2))
      ≤ ∫⁻ A in matBox b M₂ 1,
          ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
            * ENNReal.ofReal (((Matrix.of A) * (Matrix.of A)ᵀ).det ^ (-(a : ℝ) / 2)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
        filter_upwards [hae] with A hrank _hAbox
        rw [Matrix.mul_one] at hrank
        exact hpt A hrank
    _ = ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
          * ∫⁻ A in matBox b M₂ 1,
              ENNReal.ofReal (((Matrix.of A) * (Matrix.of A)ᵀ).det ^ (-(a : ℝ) / 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The shell-0 comparison target is finite** (`Wenn(I_{M₂}) < ⊤`), the banked box-clipped
determinant integral in the convergent regime `a < M₂ − b + 1`. Re-exposed here so the shell-0 uniform
bound reads with its finite majorant in one place. -/
theorem uniformWenn_target_lt_top {a b M₂ : ℕ} (hbM : b ≤ M₂) (haM : (a : ℝ) < (M₂ : ℝ) - b + 1) :
    (∫⁻ A in matBox b M₂ 1,
        ENNReal.ofReal (((Matrix.of A) * (Matrix.of A)ᵀ).det ^ (-(a : ℝ) / 2))) < ⊤ :=
  detGram_lintegral_box_lt_top hbM haM 1

end DLNFibre.DLN.RLCT
