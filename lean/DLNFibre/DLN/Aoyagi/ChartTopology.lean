import DLNFibre.DLN.Aoyagi.ThroughLayerMatrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Instances.Matrix

/-!
# Topological determinant charts for Aoyagi product reduction

This file records the elementary open-neighborhood facts for the selected
top-left determinant chart.  It does not state rank-stratum or RLCT
consequences.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section DeterminantChart

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
variable {ι μ ν : Type*} [Fintype ι] [DecidableEq ι]

omit [IsTopologicalRing K] in
/-- The unit locus in a ring with open units is open. -/
theorem isOpen_setOf_isUnit : IsOpen ({x : K | IsUnit x}) := by
  simpa [IsUnit] using (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).isOpen_range

omit [CommRing K] [IsTopologicalRing K] [IsOpenUnits K] [Fintype ι] [DecidableEq ι] in
/-- The selected top-left corner is a continuous function of the matrix entries. -/
theorem continuous_topLeftCorner :
    Continuous (fun M : Matrix (ι ⊕ μ) (ι ⊕ ν) K ↦ topLeftCorner M) := by
  exact continuous_id.matrix_submatrix Sum.inl Sum.inl

omit [IsOpenUnits K] in
/-- The determinant of the selected top-left corner is continuous. -/
theorem continuous_det_topLeftCorner :
    Continuous (fun M : Matrix (ι ⊕ μ) (ι ⊕ ν) K ↦ (topLeftCorner M).det) :=
  continuous_topLeftCorner.matrix_det

/-- The selected determinant chart is open in the ambient matrix space. -/
theorem isOpen_identityCornerDetChart :
    IsOpen ({M : Matrix (ι ⊕ μ) (ι ⊕ ν) K | identityCornerDetChart M}) := by
  dsimp [identityCornerDetChart]
  exact continuous_det_topLeftCorner.isOpen_preimage _ isOpen_setOf_isUnit

/-- A point in the selected determinant chart has that chart as a neighborhood. -/
theorem identityCornerDetChart_mem_nhds
    {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K} (hM : identityCornerDetChart M) :
    {N : Matrix (ι ⊕ μ) (ι ⊕ ν) K | identityCornerDetChart N} ∈ nhds M :=
  IsOpen.mem_nhds isOpen_identityCornerDetChart hM

/-- Left multiplication pulls the selected determinant chart back to a neighborhood of
the untransformed matrix. -/
theorem leftMul_identityCornerDetChart_mem_nhds
    [Fintype μ]
    (A : Matrix (ι ⊕ μ) (ι ⊕ μ) K)
    {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K}
    (hAM : identityCornerDetChart (A * M)) :
    {N : Matrix (ι ⊕ μ) (ι ⊕ ν) K | identityCornerDetChart (A * N)} ∈ nhds M := by
  exact (continuous_const.matrix_mul continuous_id).continuousAt.preimage_mem_nhds
    (identityCornerDetChart_mem_nhds hAM)

/-- Upper-block left multiplication pulls the selected determinant chart back to a
neighborhood of the untransformed matrix. -/
theorem fromBlocks_leftMul_identityCornerDetChart_mem_nhds
    [Fintype μ] [DecidableEq μ]
    (F : Matrix ι μ K)
    {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K}
    (hFM : identityCornerDetChart
      (fromBlocks (1 : Matrix ι ι K) F 0 (1 : Matrix μ μ K) * M)) :
    {N : Matrix (ι ⊕ μ) (ι ⊕ ν) K |
      identityCornerDetChart
        (fromBlocks (1 : Matrix ι ι K) F 0 (1 : Matrix μ μ K) * N)} ∈ nhds M :=
  leftMul_identityCornerDetChart_mem_nhds
    (fromBlocks (1 : Matrix ι ι K) F 0 (1 : Matrix μ μ K)) hFM

/-- Identity-corner form gives an open determinant-chart neighborhood of the matrix. -/
theorem identityCornerForm_mem_nhds_identityCornerDetChart
    {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K} (hM : identityCornerForm M) :
    {N : Matrix (ι ⊕ μ) (ι ⊕ ν) K | identityCornerDetChart N} ∈ nhds M :=
  identityCornerDetChart_mem_nhds (identityCornerDetChart_of_identityCornerForm hM)

end DeterminantChart

section ContinuousLinearMapCoordinates

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable {ι μ E F : Type*} [Fintype ι] [DecidableEq ι] [Finite μ]
  [AddCommGroup E] [TopologicalSpace E] [Module K E] [ContinuousSMul K E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
  [Module K F] [ContinuousSMul K F]

/-- Fixed bases identify continuous linear maps with matrices continuously. -/
theorem continuous_linearMap_toMatrix
    (bE : Module.Basis ι K E) (bF : Module.Basis μ K F) :
    Continuous (fun f : E →L[K] F ↦ LinearMap.toMatrix bE bF (f : E →ₗ[K] F)) := by
  classical
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  change Continuous (fun f : E →L[K] F ↦ LinearMap.toMatrix bE bF (f : E →ₗ[K] F) i j)
  rw [show (fun f : E →L[K] F ↦ LinearMap.toMatrix bE bF (f : E →ₗ[K] F) i j) =
      (fun f : E →L[K] F ↦ bF.repr (f (bE j)) i) by
    funext f
    simpa using (LinearMap.toMatrix_apply bE bF (f : E →ₗ[K] F) i j)]
  exact (continuous_apply i).comp
    ((Module.Basis.continuous_coe_repr bF).comp (continuous_eval_const (bE j)))

end ContinuousLinearMapCoordinates

section ChartLocalSuffixStateTopology

variable {K : Type*} [NontriviallyNormedField K]
variable {α : Type*} [TopologicalSpace α] {x₀ : α}
variable {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
  [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]

/-- Matrix inversion is continuous at a matrix with unit determinant over a normed field. -/
theorem continuousAt_matrix_inv_of_isUnit_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι K}
    (hA : IsUnit A.det) : ContinuousAt Inv.inv A := by
  exact continuousAt_matrix_inv A (by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hA.ne_zero)

/-- The accumulated upper block produced by one deterministic suffix-state step varies
continuously with the edge and the previous accumulated upper block. -/
theorem continuousAt_chartLocalSuffixState_step_B
    (E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : α → ChartLocalSuffixState ρ κ K j p.succ)
    (hE : ContinuousAt (fun x : α ↦ E x p) x₀)
    (hB : ContinuousAt (fun x : α ↦ (S x).B) x₀)
    (hchart :
      identityCornerDetChart (ChartLocalSuffixState.transformedEdge (E x₀) p (S x₀))) :
    ContinuousAt (fun x : α ↦ (ChartLocalSuffixState.step (E x) p (S x)).B) x₀ := by
  let M : α → Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K :=
    fun x ↦ ChartLocalSuffixState.transformedEdge (E x) p (S x)
  have hleft : ContinuousAt
      (fun x : α ↦
        fromBlocks (1 : Matrix ρ ρ K) (S x).B 0
          (1 : Matrix (κ p.succ) (κ p.succ) K)) x₀ := by
    have hfrom : Continuous
        (fun B : Matrix ρ (κ p.succ) K ↦
          fromBlocks (1 : Matrix ρ ρ K) B 0
            (1 : Matrix (κ p.succ) (κ p.succ) K)) :=
      continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const
    exact hfrom.continuousAt.comp hB
  have hM : ContinuousAt M x₀ := by
    have hmul : Continuous (fun q :
        Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.succ) K ×
          Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K ↦ q.1 * q.2) :=
      continuous_fst.matrix_mul continuous_snd
    simpa [M, ChartLocalSuffixState.transformedEdge] using
      ContinuousAt.comp₂ hmul.continuousAt hleft hE
  have htop : ContinuousAt (fun x : α ↦ topLeftCorner (M x)) x₀ :=
    continuous_topLeftCorner.continuousAt.comp hM
  have htopInvBase : ContinuousAt (Inv.inv : Matrix ρ ρ K → Matrix ρ ρ K)
      (topLeftCorner (M x₀)) :=
    continuousAt_matrix_inv_of_isUnit_det (A := topLeftCorner (M x₀)) hchart
  have htopInv : ContinuousAt (fun x : α ↦ (topLeftCorner (M x))⁻¹) x₀ :=
    by
      change ContinuousAt
        ((Inv.inv : Matrix ρ ρ K → Matrix ρ ρ K) ∘
          (fun x : α ↦ topLeftCorner (M x))) x₀
      exact ContinuousAt.comp
        (x := x₀) (f := fun x : α ↦ topLeftCorner (M x))
        (g := Inv.inv) htopInvBase htop
  have hupper : ContinuousAt (fun x : α ↦ upperRightBlock (M x)) x₀ := by
    have hupper' : Continuous
        (fun M : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K ↦ upperRightBlock M) :=
      continuous_id.matrix_submatrix Sum.inl Sum.inr
    exact hupper'.continuousAt.comp hM
  have hmulB : ContinuousAt
      (fun x : α ↦ (topLeftCorner (M x))⁻¹ * upperRightBlock (M x)) x₀ := by
    have hmul : Continuous (fun q :
        Matrix ρ ρ K × Matrix ρ (κ p.castSucc) K ↦ q.1 * q.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact ContinuousAt.comp₂ hmul.continuousAt htopInv hupper
  change ContinuousAt (fun x : α ↦ (topLeftCorner (M x))⁻¹ * upperRightBlock (M x)) x₀
  exact hmulB

/-- The accumulated upper block produced by the deterministic suffix-state recursion varies
continuously with the edge family, assuming the basepoint recursive chart hypotheses. -/
theorem continuousAt_chartLocalSuffixState_suffixState_B
    (E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (hE : ContinuousAt E x₀)
    {j : Fin (N + 1)}
    (hchart : ∀ (p : Fin N) (hpj : p.succ ≤ j),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge (E x₀) p
          (ChartLocalSuffixState.suffixState (E x₀) j p.succ hpj))) :
    ∀ (i : Fin (N + 1)) (hij : i ≤ j),
      ContinuousAt
        (fun x : α ↦ (ChartLocalSuffixState.suffixState (E x) j i hij).B) x₀ := by
  intro i hij
  let motive : (m : ℕ) → m ≤ j.val → Prop := fun m hmj ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmj j.isLt⟩
    ContinuousAt
      (fun x : α ↦
        (ChartLocalSuffixState.suffixState (E x) j im (Fin.val_fin_le.mpr hmj)).B) x₀
  have hbase : motive j.val le_rfl := by
    dsimp [motive]
    simpa [ChartLocalSuffixState.suffixState_self, ChartLocalSuffixState.terminal] using
      (continuousAt_const :
        ContinuousAt (fun _x : α ↦ (0 : Matrix ρ (κ j) K)) x₀)
  have hstep : ∀ m (hms : m + 1 ≤ j.val),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (hms.trans_lt j.isLt)⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have ih' : ContinuousAt
        (fun x : α ↦ (ChartLocalSuffixState.suffixState (E x) j p.succ hpj).B) x₀ := by
      simpa [motive, p, hpj] using ih
    have hE_p : ContinuousAt (fun x : α ↦ E x p) x₀ :=
      (continuous_apply p).continuousAt.comp hE
    have hnext : ContinuousAt
        (fun x : α ↦
          (ChartLocalSuffixState.step (E x) p
            (ChartLocalSuffixState.suffixState (E x) j p.succ hpj)).B) x₀ :=
      continuousAt_chartLocalSuffixState_step_B E p
        (fun x : α ↦ ChartLocalSuffixState.suffixState (E x) j p.succ hpj)
        hE_p ih' (hchart p hpj)
    have hstate :
        (fun x : α ↦
          (ChartLocalSuffixState.suffixState (E x) j p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj)).B) =
        (fun x : α ↦
          (ChartLocalSuffixState.step (E x) p
            (ChartLocalSuffixState.suffixState (E x) j p.succ hpj)).B) := by
      funext x
      rw [ChartLocalSuffixState.suffixState_castSucc]
    rw [← hstate] at hnext
    simpa [motive, p, hpj] using hnext
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hij)
  simpa [motive] using hcanon

end ChartLocalSuffixStateTopology

section PaperOrder

universe u v

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- An adapted paper-order edge has an open selected determinant-chart neighborhood. -/
theorem paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) :
    {M : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
      identityCornerDetChart M} ∈
      nhds (paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_mem_nhds
    (identityCornerDetChart_paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p)

/-- A transformed adapted paper-order edge has an open determinant-chart neighborhood. -/
theorem unitriangular_paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) :
    {M : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
      identityCornerDetChart M} ∈
      nhds (paperUnitriangularLeft W B U₀ p F * paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_mem_nhds
    (identityCornerDetChart_unitriangular_paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p F)

end PaperOrder

end Aoyagi
end DLN
end DLNFibre
