import DLNFibre.DLN.RLCT.Validate.D1L2ExplChartClose
import DLNFibre.DLN.RLCT.Validate.D1L2SchurAssembly
import DLNFibre.DLN.RLCT.Foundations.S1ChartTransfer
import DLNFibre.Core.SchurRankZero

/-!
# `DLNFibre.DLN.RLCT.Validate.D1L2ExplChartClose2` — the `hchart` germ + Option-A wiring

Second half of the L = 2 crux close.  `D1L2ExplChartClose` banked the reindex FOUNDATION
(`e_idx`/`splitMP`/`measurePreserving_splitMP`, `roleEquiv`, `paramsEquivFlat_symm_splitMP_core`,
`dlnLoss_coreParams`).  This module builds, on top of it:

* `splitHomeoL2` — the `Homeomorph` version of `splitMP` (with the ContDiff inverse), so
  `rlctAtOn_comp_homeomorph` (needs `≃ₜ`) applies.
* the `qₑ` residual (the `₂₂` Schur residual with the banked bump-globalised inverse `G`),
  its global `ContDiff ℝ 1`, and its slice value (`Core.schur_complement_zero_of_rank_le`).
* the `hchart` germ (`schur_loss_germ_L2_rlct` ▸ `rlctAtOn_congr_germ` ▸ `rlctAtOn_comp_homeomorph`),
  the `hfact` slice factorisation (via `dlnLoss_coreParams`, `u ≡ 1`, a core-translation `e`),
  and `hRne` (`dlnLoss_deepest_core_ae_ne_zero`).
* `d1ge_L2_hAtV_explicit_close` — the crux conclusion, feeding the banked consumer
  `d1ge_L2_hAtV_of_explicit_chart`.

Single-writer: NOT in the aggregator; the controller wires `D1L2ExplChartClose2`, then
`D1L2ExplicitCoreProducer` imports it to fill the crux `d1ge_L2_hAtV_explicit`.
-/

open Matrix MeasureTheory
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

variable {H : Fin (2 + 1) → ℕ} {r : ℕ}
variable (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H (Fin.last 2)))
  (hI : Function.Injective I) (hK : Function.Injective K) (hJ : Function.Injective J)

/-! ## The `Homeomorph` version of `splitMP` (with the ContDiff inverse) -/

/-- `splitMP.symm` reads coordinate `c` off the three blocks via `e_idx.symm`. -/
theorem splitMP_symm_apply
    (q : (Fin (nRegL2 H r) → ℝ) × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDim H r) → ℝ)))
    (c : Fin (flatDim H)) :
    (splitMP I K J hI hK hJ).symm q c
      = Sum.elim q.1 (Sum.elim q.2.1 q.2.2) ((e_idx I K J hI hK hJ).symm c) := by
  have h := splitOfPartition_symm_apply (e_idx I K J hI hK hJ) q ((e_idx I K J hI hK hJ).symm c)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- `splitMP.symm` is `C^∞` (each output coordinate is a projection of one block of the input). -/
theorem contDiff_splitMP_symm :
    ContDiff ℝ (⊤ : ℕ∞) (⇑(splitMP I K J hI hK hJ).symm) := by
  rw [contDiff_pi]
  intro c
  have hfun : (fun q => (splitMP I K J hI hK hJ).symm q c)
      = fun q => Sum.elim q.1 (Sum.elim q.2.1 q.2.2) ((e_idx I K J hI hK hJ).symm c) :=
    funext fun q => splitMP_symm_apply I K J hI hK hJ q c
  rw [hfun]
  rcases h : (e_idx I K J hI hK hJ).symm c with i | (j | k)
  · simp only [Sum.elim_inl]
    exact (contDiff_apply ℝ _ i).comp contDiff_fst
  · simp only [Sum.elim_inr, Sum.elim_inl]
    exact (contDiff_apply ℝ _ j).comp (contDiff_fst.comp contDiff_snd)
  · simp only [Sum.elim_inr]
    exact (contDiff_apply ℝ _ k).comp (contDiff_snd.comp contDiff_snd)

/-- The forward `splitMP` is continuous (each block coordinate is a projection). -/
theorem continuous_splitMP : Continuous (⇑(splitMP I K J hI hK hJ)) := by
  have hc1 : Continuous fun w : Fin (flatDim H) → ℝ => (splitMP I K J hI hK hJ w).1 :=
    continuous_pi fun i => by
      have : (fun w : Fin (flatDim H) → ℝ => (splitMP I K J hI hK hJ w).1 i)
          = fun w => w (e_idx I K J hI hK hJ (Sum.inl i)) :=
        funext fun w => splitMP_reg I K J hI hK hJ w i
      rw [this]; exact continuous_apply _
  have hc2 : Continuous fun w : Fin (flatDim H) → ℝ => (splitMP I K J hI hK hJ w).2.1 :=
    continuous_pi fun j => by
      have : (fun w : Fin (flatDim H) → ℝ => (splitMP I K J hI hK hJ w).2.1 j)
          = fun w => w (e_idx I K J hI hK hJ (Sum.inr (Sum.inl j))) :=
        funext fun w => splitMP_core I K J hI hK hJ w j
      rw [this]; exact continuous_apply _
  have hc3 : Continuous fun w : Fin (flatDim H) → ℝ => (splitMP I K J hI hK hJ w).2.2 :=
    continuous_pi fun k => by
      have : (fun w : Fin (flatDim H) → ℝ => (splitMP I K J hI hK hJ w).2.2 k)
          = fun w => w (e_idx I K J hI hK hJ (Sum.inr (Sum.inr k))) :=
        funext fun w => splitMP_spec I K J hI hK hJ w k
      rw [this]; exact continuous_apply _
  exact hc1.prodMk (hc2.prodMk hc3)

/-- **The `Homeomorph` version of `splitMP`**, with the same underlying equiv (so `splitMP_reg/core/
spec`, `measurePreserving_splitMP`, and the measurable-embedding all transfer definitionally), usable
by `rlctAtOn_comp_homeomorph` (which wants `≃ₜ`). -/
noncomputable def splitHomeoL2 :
    (Fin (flatDim H) → ℝ) ≃ₜ
      (Fin (nRegL2 H r) → ℝ) × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDim H r) → ℝ)) where
  toEquiv := (splitMP I K J hI hK hJ).toEquiv
  continuous_toFun := continuous_splitMP I K J hI hK hJ
  continuous_invFun := (contDiff_splitMP_symm I K J hI hK hJ).continuous

@[simp] theorem splitHomeoL2_apply (w : Fin (flatDim H) → ℝ) :
    splitHomeoL2 I K J hI hK hJ w = splitMP I K J hI hK hJ w := rfl

theorem measurePreserving_splitHomeoL2 :
    MeasurePreserving (splitHomeoL2 I K J hI hK hJ)
      (volume : Measure (Fin (flatDim H) → ℝ)) volume :=
  measurePreserving_splitMP I K J hI hK hJ

theorem measurableEmbedding_splitHomeoL2 :
    MeasurableEmbedding (splitHomeoL2 I K J hI hK hJ) :=
  (splitMP I K J hI hK hJ).measurableEmbedding

/-- `splitHomeoL2` sends the flat origin to the split origin. -/
theorem splitHomeoL2_zero :
    splitHomeoL2 I K J hI hK hJ (0 : Fin (flatDim H) → ℝ)
      = (0 : (Fin (nRegL2 H r) → ℝ)
              × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDim H r) → ℝ))) := by
  apply Prod.ext
  · funext i; exact splitMP_reg I K J hI hK hJ 0 i
  · apply Prod.ext
    · funext j; exact splitMP_core I K J hI hK hJ 0 j
    · funext k; exact splitMP_spec I K J hI hK hJ 0 k

end DLNFibre.DLN.RLCT
