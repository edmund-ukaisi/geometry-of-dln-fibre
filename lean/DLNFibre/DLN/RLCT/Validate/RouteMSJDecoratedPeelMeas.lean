import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelMeas` — the absorption-CoV Jacobian (Phase 1)

**Thread `genm-decbuild`, Phase 1 (the measure-theoretic CoV).** The left-multiplication change of
variables underlying the peelcert absorption step (`threads/genm-peelcert/cert.md`, §"THE CoV
(i)+JACOBIAN (ii)", step 1): the pivot-row substitution `X ↦ B = P·X + B₁₂·Y` at fixed `(P,B₁₂,Y)`
carries the Lebesgue Jacobian `d(X) = |det P|^{−M₂} d(B)`.

Transcribes the banked `RouteMSJGammaAtom.lintegral_comp_rightMulₚ` pattern to LEFT multiplication,
over the COLUMN-indexed space `Fin c → Fin t → ℝ` (each `c = M₂` column left-multiplied by
`P`, so the map is the `c`-fold diagonal of `P.mulVecLin` and `LinearMap.det_pi` gives `(det P)^c`
directly — the row-indexed left-mult mixes rows and is not `pi`-diagonal). The instance diamond
(`Matrix.module` vs `NormedSpace.toModule`) that blocks feeding `RouteMSchurFrameDet.mulLeftMat` to
`map_linearMap_addHaar_eq_smul_addHaar` is avoided by staying on the raw pi type.

## What lands here (sorry-free)

* **`mulLeftₚ` / `mulLeftₚ_apply` / `det_mulLeftₚ`** — left-mult-by-`K` per column, on
  `Fin c → Fin t → ℝ`, acting `Y k ↦ K.mulVec (Y k)`, determinant `(det K)^c`.
* **`lintegral_comp_mulLeftₚ`** — the absorption Jacobian CoV (full-space): for `det K ≠ 0` and
  measurable `g`, `∫⁻ Y, g (fun k ↦ K.mulVec (Y k)) = ofReal (|det K|^c)⁻¹ · ∫⁻ Y, g Y`.

S2-FREE: the finite-dim linear-CoV Haar scaling + `det_pi`.
Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Matrix
open scoped ENNReal BigOperators

/-- **Left multiplication `Y k ↦ K · (Y k)` per column, as an endomorphism of `Fin c → Fin t → ℝ`.**
The `c`-fold diagonal `LinearMap.pi (fun k ↦ K.mulVecLin ∘ proj k)`; each column by `v ↦ K.mulVec v
= K.mulVecLin v`. -/
noncomputable def mulLeftₚ (c : ℕ) {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    (Fin c → Fin t → ℝ) →ₗ[ℝ] (Fin c → Fin t → ℝ) :=
  LinearMap.pi (fun k : Fin c =>
    (K.mulVecLin).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin c => Fin t → ℝ) k))

/-- `mulLeftₚ` is left-mult by `K` on each column: `(mulLeftₚ K Y) k = K.mulVec (Y k)`. -/
theorem mulLeftₚ_apply (c : ℕ) {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ)
    (Y : Fin c → Fin t → ℝ) (k : Fin c) : mulLeftₚ c K Y k = K.mulVec (Y k) := by
  simp only [mulLeftₚ, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Matrix.mulVecLin_apply]

/-- **The absorption cov Jacobian — `det (Y ↦ K·Y per column) = (det K)^c`.** The `c`-fold diagonal
determinant (`LinearMap.det_pi`) of the single-column map `v ↦ K.mulVec v = Matrix.toLin' K`
(`det_toLin'`), giving `∏_{k : Fin c} det K = (det K)^c`. -/
theorem det_mulLeftₚ (c : ℕ) {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    LinearMap.det (mulLeftₚ c K) = (Matrix.det K) ^ c := by
  rw [mulLeftₚ, LinearMap.det_pi]
  have hcol : ∀ _ : Fin c, LinearMap.det (K.mulVecLin) = Matrix.det K := by
    intro _
    rw [show K.mulVecLin = Matrix.toLin' K from (Matrix.toLin'_apply' K).symm,
      LinearMap.det_toLin']
  rw [Finset.prod_congr rfl (fun k _ => hcol k), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **The `lintegral` absorption CoV (invertible `K`, full space).** For a measurable
`ℝ≥0∞`-integrand `g` on `Fin c → Fin t → ℝ` and `det K ≠ 0`, precomposing with per-column
left-multiplication by `K` scales the full-space integral by the reciprocal Jacobian `|det K|^{−c}`:

    ∫⁻ Y, g (fun k ↦ K.mulVec (Y k))  =  ofReal (|det K|^c)⁻¹ · ∫⁻ Y, g Y.

`map_linearMap_addHaar_eq_smul_addHaar` (Haar scaling of the finite-dim linear cov, Jacobian
`det (mulLeftₚ K) = (det K)^c` by `det_mulLeftₚ`) + `lintegral_map` + `lintegral_smul_measure`. -/
theorem lintegral_comp_mulLeftₚ (c : ℕ) {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) (hK : K.det ≠ 0)
    (g : (Fin c → Fin t → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ Y : Fin c → Fin t → ℝ, g (fun k => K.mulVec (Y k))
      = ENNReal.ofReal (|K.det| ^ c)⁻¹ * ∫⁻ Y : Fin c → Fin t → ℝ, g Y := by
  have hdet : LinearMap.det (mulLeftₚ c K) ≠ 0 := by
    rw [det_mulLeftₚ]; exact pow_ne_zero _ hK
  have hfmeas : Measurable (mulLeftₚ c K) :=
    (mulLeftₚ c K).continuous_of_finiteDimensional.measurable
  show ∫⁻ Y : Fin c → Fin t → ℝ, g (mulLeftₚ c K Y)
      = ENNReal.ofReal (|K.det| ^ c)⁻¹ * ∫⁻ Y : Fin c → Fin t → ℝ, g Y
  rw [← lintegral_map hg hfmeas,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet,
    lintegral_smul_measure, det_mulLeftₚ,
    show |((K.det) ^ c)⁻¹| = (|K.det| ^ c)⁻¹ from by rw [abs_inv, abs_pow], smul_eq_mul]

end DLNFibre.DLN.RLCT
