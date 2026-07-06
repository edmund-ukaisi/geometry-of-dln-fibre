import DLNFibre.DLN.RLCT.Validate.D1L2PhiExpl
import DLNFibre.DLN.RLCT.Validate.DeepestSchurSmooth

/-!
# `DLNFibre.DLN.RLCT.Validate.D1L2PhiExplClose` — reusable bricks for the Option-A crux close

Toward closing the L = 2 headline crux `d1ge_L2_hAtV_explicit` by feeding the banked consumer
`d1ge_L2_hAtV_of_explicit_chart` (`D1L2SchurAssembly`) with the germ `schur_loss_germ_L2_rlct`
(`D1L2PhiExpl`) via **Option A**. This module banks the ONE analytic brick that any explicit-`qₑ`
construction needs: a **globally `ContDiff` matrix inverse** agreeing with `Matrix.inv` near a
fixed nonsingular pivot. The residual `qₑ`'s dependence on the *product-pivot* inverse
`(M11)⁻¹` is only smooth where `det M11 ≠ 0`; the germ transfer (`rlctAtOn_congr_germ`) only needs
`qₑ` to match the raw `₂₂` corner NEAR the base point, so the inverse may be bump-globalised — this
lemma is exactly that globalisation, and its slice value `G(M11₀) = M11₀⁻¹` is `rfl`-exact (the germ
agrees at the pivot), which the slice factorisation `hfact` consumes.

Status: this brick is sorry-free. The remaining Option-A assembly (the flat-coordinate reindex
`Fin (flatDim H) → ℝ ≃ₜ (Fin nRegL2 → ℝ) × ((Fin (flatDim (H − r)) → ℝ) × (Fin specDim → ℝ))`
aligned to `blockFlatEquiv_L2`'s block structure, `qₑ`'s global `ContDiff`, `hchart` via
`rlctAtOn_comp_homeomorph` + `rlctAtOn_congr_germ`, `hfact` via `schur_complement_zero_of_rank_le`,
`hRne` via `dlnLoss_deepest_core_ae_ne_zero`) is a larger sub-tide (see the thread note): it is NOT
built here, and the crux `d1ge_L2_hAtV_explicit` remains an honest `sorry` in
`D1L2ExplicitCoreProducer` — this module does NOT wire it, to avoid laundering
`aoyagi_learning_coefficient_L2`.
-/

open Matrix
open scoped Topology Matrix.Norms.Elementwise

namespace DLNFibre.DLN.RLCT

/-- **The matrix inverse is `ContDiffOn` on the nonsingular locus.** Each entry
`M⁻¹ i j = (det M)⁻¹ · adjugate M i j` is `ContDiffAt` at any `M` with `det M ≠ 0`
(`contDiffAt_matrix_inv_entry_of_det_ne_zero` with `A = id`); assembling entrywise
(`contDiffOn_pi`) gives the matrix-valued `ContDiffOn`. -/
theorem contDiffOn_matrix_inv {n : ℕ} :
    ContDiffOn ℝ 1 (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹)
      {M : Matrix (Fin n) (Fin n) ℝ | M.det ≠ 0} := by
  have h1le : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [show (1 : WithTop ℕ∞) = ((1 : ℕ∞) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  intro M hM
  refine ContDiffAt.contDiffWithinAt ?_
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
  exact (contDiffAt_matrix_inv_entry_of_det_ne_zero
    (A := fun y : Matrix (Fin n) (Fin n) ℝ => y) (fun a b => by fun_prop) hM i j).of_le h1le

/-- **A globally `ContDiff` inverse agreeing with `Matrix.inv` near a fixed nonsingular pivot.**
Bump-globalise `contDiffOn_matrix_inv` (which is `ContDiffOn` on the open nonsingular locus) around
`P₀` (`det P₀ ≠ 0`) via `exists_contDiff_eventuallyEq_of_contDiffOn`: there is a GLOBAL `ContDiff ℝ 1`
matrix map `G` with `G =ᶠ[𝓝 P₀] (·⁻¹)`. This is the smooth surrogate for the product-pivot inverse in
the explicit residual `qₑ`; near the base point `G` equals the true inverse (so `qₑ` matches the raw
`₂₂` corner for the germ transfer), while being defined and smooth EVERYWHERE (so `qₑ` is globally
`ContDiff ℝ 1`, as the consumer `d1ge_L2_hAtV_of_explicit_chart` requires). -/
theorem exists_contDiff_matrixInv_eventuallyEq {n : ℕ}
    (P₀ : Matrix (Fin n) (Fin n) ℝ) (hP₀ : P₀.det ≠ 0) :
    ∃ G : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ,
      ContDiff ℝ 1 G ∧ G =ᶠ[𝓝 P₀] (fun M => M⁻¹) := by
  have hopen : IsOpen {M : Matrix (Fin n) (Fin n) ℝ | M.det ≠ 0} :=
    isOpen_ne.preimage (continuous_id.matrix_det)
  exact exists_contDiff_eventuallyEq_of_contDiffOn (n := (1 : ℕ∞)) hopen
    (show P₀ ∈ {M : Matrix (Fin n) (Fin n) ℝ | M.det ≠ 0} from hP₀) contDiffOn_matrix_inv

end DLNFibre.DLN.RLCT
