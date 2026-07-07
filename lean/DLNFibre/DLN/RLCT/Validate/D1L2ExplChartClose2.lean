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
open scoped ENNReal Topology BigOperators Matrix.Norms.Elementwise
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

/-! ## The regular readback (piece 1): `∑ p² = ∑ M21² + ∑ M11² + ∑ M12²`

Each regular flat coordinate `x (e_idx (inl ρ))` equals the corresponding `blockFlatEquiv_L2` block
entry (M21 for the `L0.₂₁` role, M11/M12 for the `L1.₁₁,₁₂` roles) — the same per-role decode as
`paramsEquivFlat_symm_splitMP_core`. No constant shift (the reg residuals are the RAW block entries). -/

/-- The M21 regular role decodes to the `L0.₂₁` block entry. -/
theorem reg_entry_M21 (x : Fin (flatDim H) → ℝ) (a : Fin (H 0 - r)) (k : Fin r) :
    x (Fintype.equivFin (FlatIdx H) (roleToFlat I K J hI hK hJ (Sum.inl (Sum.inl (a, k)))))
      = (blockFlatEquiv_L2 H r I K J hI hK hJ x).1.toBlocks₂₁ a k := by
  have hL : roleToFlat I K J hI hK hJ (Sum.inl (Sum.inl (a, k)))
      = ⟨⟨(0 : Fin 2), sumSplit I hI (Sum.inr a)⟩, sumSplit K hK (Sum.inl k)⟩ := rfl
  rw [hL, blockFlatEquiv_L2_fst]
  simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, paramsEquivFlatLinear_symm_coe]
  exact (paramsEquivFlat_symm_entry H x 0 (sumSplit I hI (Sum.inr a)) (sumSplit K hK (Sum.inl k))).symm

/-- The M11 regular role decodes to the `L1.₁₁` block entry. -/
theorem reg_entry_M11 (x : Fin (flatDim H) → ℝ) (k k' : Fin r) :
    x (Fintype.equivFin (FlatIdx H) (roleToFlat I K J hI hK hJ (Sum.inl (Sum.inr (k, Sum.inl k')))))
      = (blockFlatEquiv_L2 H r I K J hI hK hJ x).2.toBlocks₁₁ k k' := by
  have hL : roleToFlat I K J hI hK hJ (Sum.inl (Sum.inr (k, Sum.inl k')))
      = ⟨⟨(1 : Fin 2), sumSplit K hK (Sum.inl k)⟩, sumSplit J hJ (Sum.inl k')⟩ := rfl
  rw [hL, blockFlatEquiv_L2_snd]
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, paramsEquivFlatLinear_symm_coe]
  exact (paramsEquivFlat_symm_entry H x 1 (sumSplit K hK (Sum.inl k)) (sumSplit J hJ (Sum.inl k'))).symm

/-- The M12 regular role decodes to the `L1.₁₂` block entry. -/
theorem reg_entry_M12 (x : Fin (flatDim H) → ℝ) (k : Fin r) (b : Fin (H (Fin.last 2) - r)) :
    x (Fintype.equivFin (FlatIdx H) (roleToFlat I K J hI hK hJ (Sum.inl (Sum.inr (k, Sum.inr b)))))
      = (blockFlatEquiv_L2 H r I K J hI hK hJ x).2.toBlocks₁₂ k b := by
  have hL : roleToFlat I K J hI hK hJ (Sum.inl (Sum.inr (k, Sum.inr b)))
      = ⟨⟨(1 : Fin 2), sumSplit K hK (Sum.inl k)⟩, sumSplit J hJ (Sum.inr b)⟩ := rfl
  rw [hL, blockFlatEquiv_L2_snd]
  simp only [Matrix.toBlocks₁₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, paramsEquivFlatLinear_symm_coe]
  exact (paramsEquivFlat_symm_entry H x 1 (sumSplit K hK (Sum.inl k)) (sumSplit J hJ (Sum.inr b))).symm

/-- `e_idx` on the reg slot: `= equivFin ∘ roleToFlat ∘ inl ∘ regEquivFin`. -/
theorem e_idx_reg (i : Fin (nRegL2 H r)) :
    e_idx I K J hI hK hJ (Sum.inl i)
      = Fintype.equivFin (FlatIdx H)
          (roleToFlat I K J hI hK hJ (Sum.inl (regEquivFin I J hI hJ i))) := rfl

/-- **The regular readback.** The sum of squares of the `nRegL2` regular flat coordinates equals the
sum of squares of the three regular blocks `M21` (`L0.₂₁`), `M11` (`L1.₁₁`), `M12` (`L1.₁₂`) of
`blockFlatEquiv_L2 x`. Pure coordinate reindex (`regEquivFin` + the `RegIdx` sum split), no shift. -/
theorem reg_readback (x : Fin (flatDim H) → ℝ) :
    ∑ i, (splitMP I K J hI hK hJ x).1 i ^ 2
      = (∑ a : Fin (H 0 - r), ∑ k : Fin r,
            ((blockFlatEquiv_L2 H r I K J hI hK hJ x).1.toBlocks₂₁ a k) ^ 2)
        + ((∑ k : Fin r, ∑ k' : Fin r,
              ((blockFlatEquiv_L2 H r I K J hI hK hJ x).2.toBlocks₁₁ k k') ^ 2)
          + (∑ k : Fin r, ∑ b : Fin (H (Fin.last 2) - r),
              ((blockFlatEquiv_L2 H r I K J hI hK hJ x).2.toBlocks₁₂ k b) ^ 2)) := by
  have hstep : ∀ i : Fin (nRegL2 H r), (splitMP I K J hI hK hJ x).1 i
      = x (Fintype.equivFin (FlatIdx H)
          (roleToFlat I K J hI hK hJ (Sum.inl (regEquivFin I J hI hJ i)))) := by
    intro i; rw [splitMP_reg, e_idx_reg]
  simp_rw [hstep]
  rw [Equiv.sum_comp (regEquivFin I J hI hJ)
    (fun ρ => (x (Fintype.equivFin (FlatIdx H)
      (roleToFlat I K J hI hK hJ (Sum.inl ρ)))) ^ 2)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, reg_entry_M21, reg_entry_M11, reg_entry_M12]
  rw [Finset.sum_add_distrib]

/-! ## The explicit residual `qₑ` (the `₂₂` Schur residual, bump-globalised inverse `G`) -/

variable {N : WithTop ℕ∞}

/-- Entry of a `ContDiff` matrix-valued map is `ContDiff`. -/
theorem contDiff_matrixEntry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {mm nn : Type*} [Fintype mm] [Fintype nn]
    {f : X → Matrix mm nn ℝ} (hf : ContDiff ℝ N f) (i : mm) (j : nn) :
    ContDiff ℝ N (fun x => f x i j) :=
  (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (nn → ℝ) i).comp hf)

/-- A matrix-valued map is `ContDiff` iff each entry is (elementwise-norm = Pi topology). -/
theorem contDiff_matrix_of_entries {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {mm nn : Type*} [Fintype mm] [Fintype nn]
    {f : X → Matrix mm nn ℝ} (h : ∀ i j, ContDiff ℝ N (fun x => f x i j)) :
    ContDiff ℝ N f :=
  contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => h i j

/-- Global entrywise `ContDiff` matrix multiplication (the `ContDiff` analogue of
`contDiffAt_matrix_mul_entry`). -/
theorem contDiff_matrix_mul_entry {X mm nn pp : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype nn]
    {A : X → Matrix mm nn ℝ} {B : X → Matrix nn pp ℝ}
    (hA : ∀ i k, ContDiff ℝ N (fun x => A x i k))
    (hB : ∀ k j, ContDiff ℝ N (fun x => B x k j)) (i : mm) (j : pp) :
    ContDiff ℝ N (fun x => (A x * B x) i j) := by
  have heq : (fun x => (A x * B x) i j) = fun x => ∑ k, A x i k * B x k j := by
    funext x; rw [Matrix.mul_apply]
  rw [heq]; exact ContDiff.sum (fun k _ => (hA i k).mul (hB k j))

/-- The block chart `blockFlatEquiv_L2 ∘ splitHomeoL2.symm` is `C^∞` (a CLE precomposed with the
`C^∞` split inverse). -/
theorem contDiff_bChart :
    ContDiff ℝ (⊤ : ℕ∞) (fun py => blockFlatEquiv_L2 H r I K J hI hK hJ
      ((splitHomeoL2 I K J hI hK hJ).symm py)) :=
  (blockFlatEquiv_L2 H r I K J hI hK hJ).contDiff.comp (contDiff_splitMP_symm I K J hI hK hJ)

/-- The block matrix `Q py = blockFlatEquiv_L2 (splitHomeoL2.symm py) + C₀`, whose `₂₂` Schur residual
(with the bump-globalised inverse `G`) is `qResid`. -/
noncomputable def qBlock (C₀ : BlockParamsL2 H r)
    (py : (Fin (nRegL2 H r) → ℝ)
      × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDim H r) → ℝ))) : BlockParamsL2 H r :=
  blockFlatEquiv_L2 H r I K J hI hK hJ ((splitHomeoL2 I K J hI hK hJ).symm py) + C₀

/-- The first-layer block of `qBlock` is entrywise `C^∞`. -/
theorem contDiff_qBlock_fst_entry (C₀ : BlockParamsL2 H r)
    (i : Fin r ⊕ Fin (H 0 - r)) (j : Fin r ⊕ Fin (H 1 - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun py => (qBlock I K J hI hK hJ C₀ py).1 i j) :=
  contDiff_matrixEntry
    (contDiff_fst.comp ((contDiff_bChart I K J hI hK hJ).add contDiff_const)) i j

/-- The second-layer block of `qBlock` is entrywise `C^∞`. -/
theorem contDiff_qBlock_snd_entry (C₀ : BlockParamsL2 H r)
    (i : Fin r ⊕ Fin (H 1 - r)) (j : Fin r ⊕ Fin (H (Fin.last 2) - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun py => (qBlock I K J hI hK hJ C₀ py).2 i j) :=
  contDiff_matrixEntry
    (contDiff_snd.comp ((contDiff_bChart I K J hI hK hJ).add contDiff_const)) i j

/-- The `₂₂` Schur residual MATRIX (bump-globalised inverse `G`):
`M21·G(M11)·M12 + A0red·A1red − Br₂₂` read off `qBlock`. -/
noncomputable def qResidMat (C₀ : BlockParamsL2 H r)
    (Br022 : Matrix (Fin (H 0 - r)) (Fin (H 2 - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ)
    (py : (Fin (nRegL2 H r) → ℝ)
      × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDim H r) → ℝ))) :
    Matrix (Fin (H 0 - r)) (Fin (H 2 - r)) ℝ :=
  (qBlock I K J hI hK hJ C₀ py).1.toBlocks₂₁ * G (qBlock I K J hI hK hJ C₀ py).2.toBlocks₁₁
      * (qBlock I K J hI hK hJ C₀ py).2.toBlocks₁₂
    + (qBlock I K J hI hK hJ C₀ py).1.toBlocks₂₂ * (qBlock I K J hI hK hJ C₀ py).2.toBlocks₂₂
    - Br022

/-- **The explicit `₂₂` Schur residual `qₑ`** (bump-globalised inverse `G`): the flattened
`qResidMat`, as a `EuclideanSpace` vector. -/
noncomputable def qResid (C₀ : BlockParamsL2 H r)
    (Br022 : Matrix (Fin (H 0 - r)) (Fin (H 2 - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) :
    (Fin (nRegL2 H r) → ℝ) × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDim H r) → ℝ))
      → EuclideanSpace ℝ (Fin ((H 0 - r) * (H 2 - r))) := fun py =>
  (EuclideanSpace.equiv (Fin ((H 0 - r) * (H 2 - r))) ℝ).symm
    (fun i => qResidMat I K J hI hK hJ C₀ Br022 G py
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

/-- **`qResid` is globally `ContDiff ℝ 1`** (given `G` is `ContDiff ℝ 1`). The three regular blocks are
`C^∞` in `py` (`qBlock` entries); `G(M11)` is the `C¹` `G` composed with the `C^∞` `M11` block; the
two matrix products and the constant `Br₂₂` assemble entrywise. -/
theorem contDiff_qResid (C₀ : BlockParamsL2 H r)
    (Br022 : Matrix (Fin (H 0 - r)) (Fin (H 2 - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (qResid I K J hI hK hJ C₀ Br022 G) := by
  have h1top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  refine contDiff_euclidean.mpr fun i => ?_
  -- `G(M11)` block entries are `C¹`.
  have hGM11 : ∀ k k' : Fin r,
      ContDiff ℝ 1 (fun py => (G (qBlock I K J hI hK hJ C₀ py).2.toBlocks₁₁) k k') := by
    intro k k'
    have hM11 : ContDiff ℝ 1 (fun py => (qBlock I K J hI hK hJ C₀ py).2.toBlocks₁₁) :=
      contDiff_matrix_of_entries fun i' j' =>
        (contDiff_qBlock_snd_entry I K J hI hK hJ C₀ (Sum.inl i') (Sum.inl j')).of_le h1top
    exact contDiff_matrixEntry (hG.comp hM11) k k'
  -- the two matrix products, entrywise `C¹`.
  set a := (finProdFinEquiv.symm i).1
  set b := (finProdFinEquiv.symm i).2
  have hProd1 : ContDiff ℝ 1 (fun py =>
      ((qBlock I K J hI hK hJ C₀ py).1.toBlocks₂₁ * G (qBlock I K J hI hK hJ C₀ py).2.toBlocks₁₁
        * (qBlock I K J hI hK hJ C₀ py).2.toBlocks₁₂) a b) := by
    refine contDiff_matrix_mul_entry
      (fun i' k' => contDiff_matrix_mul_entry
        (fun a' k'' => (contDiff_qBlock_fst_entry I K J hI hK hJ C₀ (Sum.inr a') (Sum.inl k'')).of_le
          h1top) (fun k'' k''' => hGM11 k'' k''') i' k') ?_ a b
    intro k' j'
    exact (contDiff_qBlock_snd_entry I K J hI hK hJ C₀ (Sum.inl k') (Sum.inr j')).of_le h1top
  have hProd2 : ContDiff ℝ 1 (fun py =>
      ((qBlock I K J hI hK hJ C₀ py).1.toBlocks₂₂ * (qBlock I K J hI hK hJ C₀ py).2.toBlocks₂₂) a b) :=
    contDiff_matrix_mul_entry
      (fun a' k' => (contDiff_qBlock_fst_entry I K J hI hK hJ C₀ (Sum.inr a') (Sum.inr k')).of_le
        h1top)
      (fun k' b' => (contDiff_qBlock_snd_entry I K J hI hK hJ C₀ (Sum.inr k') (Sum.inr b')).of_le
        h1top) a b
  have hfun : (fun py => qResid I K J hI hK hJ C₀ Br022 G py i)
      = fun py => ((qBlock I K J hI hK hJ C₀ py).1.toBlocks₂₁
            * G (qBlock I K J hI hK hJ C₀ py).2.toBlocks₁₁
            * (qBlock I K J hI hK hJ C₀ py).2.toBlocks₁₂) a b
          + ((qBlock I K J hI hK hJ C₀ py).1.toBlocks₂₂
            * (qBlock I K J hI hK hJ C₀ py).2.toBlocks₂₂) a b
          - Br022 a b := by
    funext py
    show qResidMat I K J hI hK hJ C₀ Br022 G py a b = _
    simp only [qResidMat, Matrix.sub_apply, Matrix.add_apply]
  rw [hfun]
  exact (hProd1.add hProd2).sub contDiff_const

end DLNFibre.DLN.RLCT
