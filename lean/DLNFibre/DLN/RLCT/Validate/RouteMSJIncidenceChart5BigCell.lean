/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.SchurChartIff
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelMeas
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Instances.Matrix

set_option linter.style.longLine false

/-!
# `RouteMSJIncidenceChart5BigCell` — Brick D piece (ii): the determinantal big-cell CoV of `W`

**Thread `genm-sj5-chart5`, aoyagi-full Stage 2.** Chart (5) of the joint incidence-rank resolution
(`genm-incidencepp/incidence-cert.md` §3b(5), §3b(b)): the determinantal big-cell change of variables
for the transverse block `W`. On the chart `{det W₁₁ ≠ 0}` the block matrix
`W = [[W₁₁, W₁₂], [W₂₁, W₂₂]]` (`W₁₁ : Fin r × Fin r`, pivot) is coordinatised by

    W ↦ (W₁₁, W₁₂, W₂₁, E),   E := W₂₂ − W₂₁ · W₁₁⁻¹ · W₁₂   (the transverse Schur complement).

The map `(W₁₁, W₁₂, W₂₁, E) ↦ W` is a **translation in the `W₂₂` block** by the constant (in `E`)
shift `W₂₁ · W₁₁⁻¹ · W₁₂` (the other three blocks fixed), so its Jacobian is `≡ 1` — verified
`inc_bigcell.py` (`|det| = 1` for `(u,d,ℓ) ∈ {(2,2,1),(2,4,1),(3,3,1),(3,3,2),(3,4,2)}`).

⚠ **The `|det DΦ| ≡ 1` here is specific to chart (5)'s pure `W₂₂`-translation structure.** It is NOT a
dropped/omitted Jacobian: chart (5) genuinely has unit Jacobian. The nontrivial monomial power
`|det D|^{n−b−a−u}` of the joint resolution lives in the *linear* `Qb`-minor chart (1) + the `B`-shear
chart (3) (`RouteMSJIncidenceChart.lean`), which compose to the cert's net power at the **assembly** —
not here. (bltj guard 2, 2026-07-15.)

## What lands here (sorry-free)

* **`chart5Shift` / `chart5Shift_measurable`** — the Schur shift `C · A⁻¹ · B` as a measurable
  `ℝ`-matrix-valued map on the fixed-block product (over the raw pi type, dodging the `Matrix.module`
  vs `NormedSpace.toModule` measure diamond — lean/CLAUDE.md).
* **`chart5_bigcell_cov`** — the big-cell CoV, Jacobian `≡ 1` (G1). For any measurable `ℝ≥0∞`-integrand
  `f` on the block product, the `W₂₂ ↦ E`-translation preserves the lintegral:

      ∫⁻ (abc, E), f (abc, E + C·A⁻¹·B)  =  ∫⁻ (abc, W₂₂), f (abc, W₂₂).

  This is an **∫-level identity** (Fubini + Haar translation-invariance of the last block), never a
  pointwise bound — the domination on the `σ_min(Q_p)→0` locus is genuinely integrated (bltj guard 1).
  Holds **unconditionally** (no `det W₁₁ ≠ 0` needed): the shear is measure-preserving everywhere.
* **`chart5_rank_eq` / `chart5_rank_le_iff_schur`** — the block-LU rank identity `rank W = r + rank E`
  and `{rank W ≤ r} = {E = 0}`, the chart-5 form of the banked `Core.SchurChartIff` (needs
  `IsUnit W₁₁.det`).
* **`chart5_rank_le_iff_reassembled`** — the bridge tying the two: in the CoV `E`-coordinates,
  `{rank W ≤ r} = {E = 0}` (a coordinate slice). Together with `chart5_bigcell_cov` this is the
  determinantal big-cell resolution: the rank-drop locus becomes the transverse coordinate slice
  `{E = 0}`, with the residual integral in unit-Jacobian `E`-coordinates.

**Scope.** This file is the *individual* chart-(5) CoV + rank geometry; it is TRUE regardless of the
`genm-bltj` gate. The finite-minor atlas gluing and the union/coverage claim (piece (v)) are the
assembly's concern and stay parked. Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Matrix
open scoped ENNReal BigOperators

section Chart5

/-- The three fixed blocks of the chart-(5) coordinatisation: the pivot `W₁₁ : Fin r × Fin r`, the
top-right `W₁₂ : Fin r × Fin t`, and the bottom-left `W₂₁ : Fin s × Fin r`, over the raw pi type
(so the product carries a `MeasureSpace`; `Matrix` does not — the measure diamond). -/
abbrev Chart5FixedBlocks (r s t : ℕ) :=
  (Fin r → Fin r → ℝ) × (Fin r → Fin t → ℝ) × (Fin s → Fin r → ℝ)

variable {r s t : ℕ}

/-- The Schur shift `W₂₁ · W₁₁⁻¹ · W₁₂` (`= C · A⁻¹ · B`), the constant-in-`E` translation of the
`W₂₂` block that reconstructs `W₂₂ = E + W₂₁ W₁₁⁻¹ W₁₂` from the transverse Schur coordinate `E`. -/
noncomputable def chart5Shift (abc : Chart5FixedBlocks r s t) : Fin s → Fin t → ℝ :=
  (Matrix.of abc.2.2 * (Matrix.of abc.1)⁻¹ * Matrix.of abc.2.1 : Matrix (Fin s) (Fin t) ℝ)

/-- `chart5Shift` is measurable (over the raw pi type). The only non-continuous ingredient is the
matrix inverse `A ↦ A⁻¹ = Ring.inverse (det A) • adjugate A`, measurable entrywise since
`Ring.inverse = Inv.inv` on `ℝ` (measurable) and `det`/`adjugate` are polynomial (continuous). -/
theorem chart5Shift_measurable : Measurable (chart5Shift : Chart5FixedBlocks r s t → _) := by
  have hof : Continuous (Matrix.of : (Fin r → Fin r → ℝ) → Matrix (Fin r) (Fin r) ℝ) := continuous_id
  have hinvE : ∀ (k l : Fin r),
      Measurable (fun abc : Chart5FixedBlocks r s t => ((Matrix.of abc.1)⁻¹) k l) := by
    intro k l
    simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    have hdet : Measurable (fun abc : Chart5FixedBlocks r s t => Ring.inverse (Matrix.of abc.1).det) := by
      rw [Ring.inverse_eq_inv']
      exact measurable_inv.comp ((Continuous.matrix_det hof).measurable.comp measurable_fst)
    have hadj : Measurable (fun abc : Chart5FixedBlocks r s t => (Matrix.of abc.1).adjugate k l) :=
      (((Continuous.matrix_adjugate hof).matrix_elem k l).measurable).comp measurable_fst
    exact hdet.mul hadj
  rw [measurable_pi_iff]; intro i; rw [measurable_pi_iff]; intro j
  simp only [chart5Shift, Matrix.mul_apply]
  refine Finset.measurable_sum _ (fun l _ => ?_)
  refine Measurable.mul ?_ ?_
  · refine Finset.measurable_sum _ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      (measurable_snd.comp measurable_snd))).mul (hinvE k l)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply l).comp (measurable_fst.comp measurable_snd))

/-- **Chart (5): the determinantal big-cell change of variables, Jacobian `≡ 1`.** The
`W₂₂ ↦ E`-translation of the `W₂₂` block by the Schur shift `C·A⁻¹·B` preserves the Lebesgue
lintegral over the block product, for any measurable `ℝ≥0∞`-integrand `f`:

    ∫⁻ (abc, E), f (abc, E + chart5Shift abc)  =  ∫⁻ (abc, W₂₂), f (abc, W₂₂).

Fubini (`lintegral_prod`) isolates the last block; Haar translation-invariance
(`lintegral_add_right_eq_self`) closes the fibrewise identity. This is an ∫-level equality (never a
pointwise bound) and holds unconditionally — the shear is measure-preserving on all of `W`-space. -/
theorem chart5_bigcell_cov
    (f : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ), f (p.1, p.2 + chart5Shift p.1)
      = ∫⁻ p, f p := by
  have hT : Measurable (fun p : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ) =>
      ((p.1, p.2 + chart5Shift p.1) : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ))) :=
    measurable_fst.prodMk (measurable_snd.add (chart5Shift_measurable.comp measurable_fst))
  have hF : Measurable (fun p : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ) =>
      f (p.1, p.2 + chart5Shift p.1)) := hf.comp hT
  rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable, lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr (fun abc => ?_)
  exact lintegral_add_right_eq_self (fun d => f (abc, d)) (chart5Shift abc)

/-- **Block-LU rank identity (chart-5 form).** For the invertible pivot `A = W₁₁`, `rank W = r + rank E`
with `E = W₂₂ − W₂₁ W₁₁⁻¹ W₁₂` the transverse Schur complement. A chart-5-shape re-export of the banked
`Core.SchurChartIff.rank_fromBlocks_invertible₁₁`. -/
theorem chart5_rank_eq
    (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin t) ℝ)
    (C : Matrix (Fin s) (Fin r) ℝ) (D : Matrix (Fin s) (Fin t) ℝ) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D).rank = r + (D - C * A⁻¹ * B).rank :=
  Core.rank_fromBlocks_invertible₁₁ A B C D hA

/-- **`{rank W ≤ r} = {E = 0}` (chart-5 form).** On the chart `det W₁₁ ≠ 0`, the rank drops to `r`
exactly when the transverse Schur complement `E = W₂₂ − W₂₁ W₁₁⁻¹ W₁₂` vanishes. A chart-5-shape
re-export of `Core.SchurChartIff.rank_le_iff_schur_eq`. -/
theorem chart5_rank_le_iff_schur
    (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin t) ℝ)
    (C : Matrix (Fin s) (Fin r) ℝ) (D : Matrix (Fin s) (Fin t) ℝ) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D).rank ≤ r ↔ D = C * A⁻¹ * B :=
  Core.rank_le_iff_schur_eq A B C D hA

/-- **The bridge: in the CoV `E`-coordinates the rank-drop locus is the coordinate slice `{E = 0}`.**
After the `chart5_bigcell_cov` substitution `W₂₂ = E + chart5Shift`, `{rank W ≤ r} = {E = 0}` — the
determinantal big-cell resolution puts the rank-drop locus at the transverse Schur coordinate origin,
in unit-Jacobian coordinates. -/
theorem chart5_rank_le_iff_reassembled
    (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin t) ℝ)
    (C : Matrix (Fin s) (Fin r) ℝ) (E : Fin s → Fin t → ℝ) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C (E + chart5Shift (A, B, C))).rank ≤ r ↔ E = 0 := by
  rw [chart5_rank_le_iff_schur A B C _ hA]
  -- goal: `E + chart5Shift (A,B,C) = C · A⁻¹ · B ↔ E = 0`, and `chart5Shift (A,B,C) = C · A⁻¹ · B`.
  constructor
  · intro h
    have hX : E + chart5Shift (A, B, C) = (0 : Fin s → Fin t → ℝ) + chart5Shift (A, B, C) := by
      rw [zero_add]; exact h
    exact add_right_cancel hX
  · intro h
    rw [h, zero_add]
    rfl

/-- Non-vacuity witness (the `(2,2,1)`-minor cell): `W₁₁ = [1]` invertible, `W = [[1,0],[0,0]]` has
`rank ≤ 1`, its transverse Schur complement `E = W₂₂ − W₂₁ W₁₁⁻¹ W₁₂ = 0` (the rank-drop locus). -/
example :
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)).rank ≤ 1 :=
  (chart5_rank_le_iff_schur 1 0 0 0 (by simp)).mpr (by simp)

end Chart5

end DLNFibre.DLN.RLCT
