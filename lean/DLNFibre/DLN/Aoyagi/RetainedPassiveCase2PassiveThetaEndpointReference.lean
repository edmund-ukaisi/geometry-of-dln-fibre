import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure

/-!
# Case 2 passive theta endpoint reference measure

This file names the concrete coordinate-product reference measure on the full
Case 2 passive-theta source.  It is only a reference-measure and support layer:
it does not prove the endpoint determinant-chart change of variables, Haar
normalization, source-prior transport, normal crossings, pole order, or RLCT
extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

/-- Coordinate-product Lebesgue reference measure on a real matrix type,
aligned with the Pi measurable-space instance on matrix entries. -/
noncomputable def matrixEntryReferenceMeasure
    (m n : Type*) [Fintype m] [Fintype n] :
    Measure (Matrix m n ℝ) :=
  Measure.pi (fun _ : m => Measure.pi (fun _ : n => volume))

set_option linter.style.longLine false in
/-- The coordinate-product Lebesgue reference measure on a finite real matrix
type is sigma-finite. -/
theorem sigmaFinite_matrixEntryReferenceMeasure
    (m n : Type*) [Fintype m] [Fintype n] :
    SigmaFinite (matrixEntryReferenceMeasure m n) := by
  change
    SigmaFinite
      (Measure.pi fun _ : m => Measure.pi fun _ : n => (volume : Measure ℝ))
  have hinner :
      ∀ _ : m, SigmaFinite (Measure.pi fun _ : n => (volume : Measure ℝ)) := by
    intro _
    exact Measure.pi.sigmaFinite (fun _ : n => (volume : Measure ℝ))
  exact Measure.pi.sigmaFinite
    (fun _ : m => Measure.pi fun _ : n => (volume : Measure ℝ))

set_option linter.style.longLine false in
/-- The coordinate-product Lebesgue reference measure on a finite real matrix
type is s-finite. -/
theorem sFinite_matrixEntryReferenceMeasure
    (m n : Type*) [Fintype m] [Fintype n] :
    SFinite (matrixEntryReferenceMeasure m n) := by
  haveI : SigmaFinite (matrixEntryReferenceMeasure m n) :=
    sigmaFinite_matrixEntryReferenceMeasure m n
  infer_instance

/-- Entrywise open coordinate box around a real matrix.  This is the finite
Pi-box replacement for metric balls on matrix types; it is tailored to the
coordinate-product reference measure. -/
def matrixEntryBox
    {m n : Type*} (F₀ : Matrix m n ℝ) (R : ℝ) : Set (Matrix m n ℝ) :=
  {F | ∀ i j, F i j ∈ Set.Ioo (F₀ i j - R) (F₀ i j + R)}

theorem mem_matrixEntryBox_self
    {m n : Type*} (F₀ : Matrix m n ℝ) {R : ℝ} (hR : 0 < R) :
    F₀ ∈ matrixEntryBox F₀ R := by
  intro i j
  constructor <;> linarith

theorem measurableSet_matrixEntryBox
    {m n : Type*} [Countable m] [Countable n]
    (F₀ : Matrix m n ℝ) (R : ℝ) :
    MeasurableSet (matrixEntryBox F₀ R) := by
  classical
  unfold matrixEntryBox
  rw [show
      {F : Matrix m n ℝ | ∀ i j, F i j ∈ Set.Ioo (F₀ i j - R) (F₀ i j + R)} =
        ⋂ i, ⋂ j,
          (fun F : Matrix m n ℝ => F i j) ⁻¹'
            Set.Ioo (F₀ i j - R) (F₀ i j + R) by
    ext F
    simp]
  exact MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun j => by
      have hcoord : Measurable (fun F : Matrix m n ℝ => F i j) :=
        (measurable_pi_apply j).comp
          (measurable_pi_apply i : Measurable (fun F : Matrix m n ℝ => F i))
      exact hcoord
        (measurableSet_Ioo : MeasurableSet (Set.Ioo (F₀ i j - R) (F₀ i j + R)))

set_option linter.unusedFintypeInType false in
theorem isOpen_matrixEntryBox
    {m n : Type*} [Fintype m] [Fintype n]
    (F₀ : Matrix m n ℝ) (R : ℝ) :
    IsOpen (matrixEntryBox F₀ R) := by
  classical
  have hbox :
      matrixEntryBox F₀ R =
        Set.pi Set.univ
          (fun i : m =>
            Set.pi Set.univ
              (fun j : n => Set.Ioo (F₀ i j - R) (F₀ i j + R))) := by
    ext F
    constructor
    · intro hF i _ j _
      exact hF i j
    · intro hF i j
      exact hF i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hbox]
  exact isOpen_set_pi Set.finite_univ fun i _ =>
    isOpen_set_pi Set.finite_univ fun j _ => isOpen_Ioo

set_option linter.style.longLine false in
theorem matrixEntryReferenceMeasure_matrixEntryBox_lt_top
    {m n : Type*} [Fintype m] [Fintype n]
    (F₀ : Matrix m n ℝ) (R : ℝ) :
    matrixEntryReferenceMeasure m n (matrixEntryBox F₀ R) < ∞ := by
  classical
  have hbox :
      matrixEntryBox F₀ R =
        Set.pi Set.univ
          (fun i : m =>
            Set.pi Set.univ
              (fun j : n => Set.Ioo (F₀ i j - R) (F₀ i j + R))) := by
    ext F
    constructor
    · intro hF i _ j _
      exact hF i j
    · intro hF i j
      exact hF i (Set.mem_univ i) j (Set.mem_univ j)
  rw [matrixEntryReferenceMeasure, hbox]
  change
    (Measure.pi fun i : m => Measure.pi fun j : n => volume)
      (Set.pi Set.univ
        (fun i : m => Set.pi Set.univ
          (fun j : n => Set.Ioo (F₀ i j - R) (F₀ i j + R)))) < ∞
  rw [Measure.pi_pi]
  refine ENNReal.prod_lt_top fun i _ => ?_
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top fun j _ => by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top

set_option linter.style.longLine false in
/-- A base following factor whose square reindexing has unit determinant admits
a finite measurable coordinate patch on which the determinant remains a unit
and the reindexed inverse has a uniform coordinate square-sum bound.

The patch is an entrywise coordinate box, cut by the determinant-unit locus and
by a strict inverse-square-sum sublevel set.  This supplies exactly the
finite-patch hypotheses needed by the with-following product-residual wrapper;
it does not identify this condition with any passive-theta determinant sector. -/
theorem exists_matrixEntryReferenceMeasure_finite_followingPatch_of_reindexed_det_isUnit
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (e : τ ≃ ι) (F₀ : Matrix ι τ ℝ)
    (hF₀det : IsUnit ((F₀.submatrix id e.symm).det)) :
    ∃ followingPatch : Set (Matrix ι τ ℝ), ∃ K : ℝ,
      0 < K ∧
        F₀ ∈ followingPatch ∧
        MeasurableSet followingPatch ∧
        matrixEntryReferenceMeasure ι τ followingPatch < ∞ ∧
        (∀ F ∈ followingPatch, IsUnit ((F.submatrix id e.symm).det)) ∧
        (∀ F ∈ followingPatch,
          aoyagiCoordinateSquareSum
              (fun ij : τ × ι =>
                (((F.submatrix id e.symm)⁻¹).submatrix e id) ij.1 ij.2) ≤ K) := by
  classical
  let inverseSquareSum : Matrix ι τ ℝ → ℝ := fun F =>
    aoyagiCoordinateSquareSum
      (fun ij : τ × ι =>
        (((F.submatrix id e.symm)⁻¹).submatrix e id) ij.1 ij.2)
  let K : ℝ := inverseSquareSum F₀ + 1
  let followingPatch : Set (Matrix ι τ ℝ) :=
    matrixEntryBox F₀ 1 ∩
      {F : Matrix ι τ ℝ | IsUnit ((F.submatrix id e.symm).det)} ∩
      {F : Matrix ι τ ℝ | inverseSquareSum F < K}
  have hbox_meas : MeasurableSet (matrixEntryBox F₀ 1) :=
    measurableSet_matrixEntryBox F₀ 1
  have hdet_meas :
      MeasurableSet {F : Matrix ι τ ℝ | IsUnit ((F.submatrix id e.symm).det)} := by
    have hdet_open :
        IsOpen {F : Matrix ι τ ℝ | IsUnit ((F.submatrix id e.symm).det)} := by
      exact
        ((continuous_id.matrix_submatrix id e.symm).matrix_det).isOpen_preimage
          ({a : ℝ | IsUnit a}) isOpen_setOf_isUnit
    exact hdet_open.measurableSet
  have hsub_meas : Measurable (fun F : Matrix ι τ ℝ => F.submatrix id e.symm) :=
    (continuous_id.matrix_submatrix id e.symm).measurable
  have hinv_meas :
      Measurable (fun F : Matrix ι τ ℝ => (F.submatrix id e.symm)⁻¹) :=
    measurable_matrix_inv_real.comp hsub_meas
  have hcoords_meas :
      Measurable
        (fun F : Matrix ι τ ℝ =>
          fun ij : τ × ι =>
            (((F.submatrix id e.symm)⁻¹).submatrix e id) ij.1 ij.2) := by
    refine measurable_pi_lambda _ fun ij => ?_
    exact
      (measurable_pi_apply ij.2).comp
        ((measurable_pi_apply (e ij.1)).comp hinv_meas)
  have hinvSq_meas : Measurable inverseSquareSum := by
    simpa [inverseSquareSum] using
      measurable_aoyagiCoordinateSquareSum hcoords_meas
  have hbound_meas : MeasurableSet {F : Matrix ι τ ℝ | inverseSquareSum F < K} :=
    hinvSq_meas (measurableSet_Iio : MeasurableSet (Set.Iio K))
  have hpatch_meas : MeasurableSet followingPatch := by
    exact (hbox_meas.inter hdet_meas).inter hbound_meas
  have hpatch_lt_top : matrixEntryReferenceMeasure ι τ followingPatch < ∞ := by
    have hsub : followingPatch ⊆ matrixEntryBox F₀ 1 := by
      intro F hF
      exact hF.1.1
    exact
      (measure_mono hsub).trans_lt
        (matrixEntryReferenceMeasure_matrixEntryBox_lt_top F₀ 1)
  have hF₀_box : F₀ ∈ matrixEntryBox F₀ 1 :=
    mem_matrixEntryBox_self F₀ zero_lt_one
  have hF₀_bound : inverseSquareSum F₀ < K := by
    dsimp [K]
    linarith
  have hK_pos : 0 < K := by
    have hnonneg : 0 ≤ inverseSquareSum F₀ := by
      dsimp [inverseSquareSum]
      exact aoyagiCoordinateSquareSum_nonneg _
    dsimp [K]
    linarith
  refine ⟨followingPatch, K, hK_pos, ?_, hpatch_meas, hpatch_lt_top, ?_, ?_⟩
  · exact ⟨⟨hF₀_box, hF₀det⟩, hF₀_bound⟩
  · intro F hF
    exact hF.1.2
  · intro F hF
    exact le_of_lt hF.2

set_option linter.style.longLine false in
/-- A base following factor whose square reindexing has unit determinant
admits an open finite coordinate patch on which the determinant remains a unit
and the reindexed inverse has a uniform coordinate square-sum bound.

The open patch is chosen inside the finite entrywise box around the base
factor and inside a local inverse-square-sum sublevel neighborhood. -/
theorem exists_matrixEntryReferenceMeasure_finite_open_followingPatch_of_reindexed_det_isUnit
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (e : τ ≃ ι) (F₀ : Matrix ι τ ℝ)
    (hF₀det : IsUnit ((F₀.submatrix id e.symm).det)) :
    ∃ followingPatch : Set (Matrix ι τ ℝ), ∃ K : ℝ,
      0 < K ∧
        F₀ ∈ followingPatch ∧
        IsOpen followingPatch ∧
        MeasurableSet followingPatch ∧
        matrixEntryReferenceMeasure ι τ followingPatch < ∞ ∧
        (∀ F ∈ followingPatch, IsUnit ((F.submatrix id e.symm).det)) ∧
        (∀ F ∈ followingPatch,
          aoyagiCoordinateSquareSum
              (fun ij : τ × ι =>
                (((F.submatrix id e.symm)⁻¹).submatrix e id) ij.1 ij.2) ≤ K) := by
  classical
  let inverseSquareSum : Matrix ι τ ℝ → ℝ := fun F =>
    aoyagiCoordinateSquareSum
      (fun ij : τ × ι =>
        (((F.submatrix id e.symm)⁻¹).submatrix e id) ij.1 ij.2)
  let K : ℝ := inverseSquareSum F₀ + 1
  have hsub_cont : Continuous (fun F : Matrix ι τ ℝ => F.submatrix id e.symm) :=
    continuous_id.matrix_submatrix id e.symm
  have hinv_cont :
      ContinuousAt (fun F : Matrix ι τ ℝ => (F.submatrix id e.symm)⁻¹) F₀ :=
    ContinuousAt.comp
      (x := F₀)
      (f := fun F : Matrix ι τ ℝ => F.submatrix id e.symm)
      (g := fun A : Matrix ι ι ℝ => A⁻¹)
      (continuousAt_matrix_inv_of_isUnit_det
        (A := F₀.submatrix id e.symm) hF₀det)
      hsub_cont.continuousAt
  have hcoords_cont :
      ContinuousAt
        (fun F : Matrix ι τ ℝ =>
          fun ij : τ × ι =>
            (((F.submatrix id e.symm)⁻¹).submatrix e id) ij.1 ij.2) F₀ := by
    refine continuousAt_pi.2 ?_
    intro ij
    exact
      (continuous_apply ij.2).continuousAt.comp
        ((continuous_apply (e ij.1)).continuousAt.comp hinv_cont)
  have hinvSq_cont : ContinuousAt inverseSquareSum F₀ := by
    simpa [inverseSquareSum] using
      aoyagiCoordinateSquareSum_continuousAt hcoords_cont
  have hF₀_bound : inverseSquareSum F₀ < K := by
    dsimp [K]
    linarith
  have hsublevel_nhds : {F : Matrix ι τ ℝ | inverseSquareSum F < K} ∈ nhds F₀ :=
    hinvSq_cont (isOpen_Iio.mem_nhds hF₀_bound)
  rcases mem_nhds_iff.mp hsublevel_nhds with
    ⟨Uinv, hUinv_sub, hUinv_open, hF₀_Uinv⟩
  let followingPatch : Set (Matrix ι τ ℝ) :=
    matrixEntryBox F₀ 1 ∩
      {F : Matrix ι τ ℝ | IsUnit ((F.submatrix id e.symm).det)} ∩
      Uinv
  have hbox_open : IsOpen (matrixEntryBox F₀ 1) :=
    isOpen_matrixEntryBox F₀ 1
  have hdet_open :
      IsOpen {F : Matrix ι τ ℝ | IsUnit ((F.submatrix id e.symm).det)} :=
    ((continuous_id.matrix_submatrix id e.symm).matrix_det).isOpen_preimage
      ({a : ℝ | IsUnit a}) isOpen_setOf_isUnit
  have hpatch_open : IsOpen followingPatch :=
    (hbox_open.inter hdet_open).inter hUinv_open
  have hpatch_meas : MeasurableSet followingPatch :=
    hpatch_open.measurableSet
  have hpatch_lt_top : matrixEntryReferenceMeasure ι τ followingPatch < ∞ := by
    have hsub : followingPatch ⊆ matrixEntryBox F₀ 1 := by
      intro F hF
      exact hF.1.1
    exact
      (measure_mono hsub).trans_lt
        (matrixEntryReferenceMeasure_matrixEntryBox_lt_top F₀ 1)
  have hF₀_box : F₀ ∈ matrixEntryBox F₀ 1 :=
    mem_matrixEntryBox_self F₀ zero_lt_one
  have hK_pos : 0 < K := by
    have hnonneg : 0 ≤ inverseSquareSum F₀ := by
      dsimp [inverseSquareSum]
      exact aoyagiCoordinateSquareSum_nonneg _
    dsimp [K]
    linarith
  refine
    ⟨followingPatch, K, hK_pos, ?_, hpatch_open, hpatch_meas,
      hpatch_lt_top, ?_, ?_⟩
  · exact ⟨⟨hF₀_box, hF₀det⟩, hF₀_Uinv⟩
  · intro F hF
    exact hF.1.2
  · intro F hF
    exact le_of_lt (hUinv_sub hF.2)

set_option linter.style.longLine false in
/-- Coordinate-product reference measure on the passive fields suppressed by
the reduced selected-entry section in Aoyagi Case 2. -/
noncomputable def case2PassiveThetaPassiveFieldReferenceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ) :
    Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
  let A1Measure : Measure (Fin 1 → Matrix ρ ρ ℝ) :=
    Measure.pi
      (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)
  let F2Measure :
      Measure
        (∀ p : Fin 2,
          Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ) :=
    Measure.pi
      (fun p : Fin 2 =>
        matrixEntryReferenceMeasure ρ
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))
  let A3Measure :
      Measure
        (∀ p : Fin 1,
          Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) :=
    Measure.pi
      (fun p : Fin 1 =>
        matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)
  let CtopMeasure : Measure (Matrix ρ ρ ℝ) :=
    matrixEntryReferenceMeasure ρ ρ
  let F3Measure :
      Measure
        (Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ) :=
    matrixEntryReferenceMeasure
      (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ
  A1Measure.prod (F2Measure.prod (A3Measure.prod (CtopMeasure.prod F3Measure)))

set_option linter.style.longLine false in
/-- The coordinate-product reference measure on the passive fields is
sigma-finite. -/
theorem sigmaFinite_case2PassiveThetaPassiveFieldReferenceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ) :
    SigmaFinite
      (case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J) := by
  dsimp [case2PassiveThetaPassiveFieldReferenceMeasure]
  haveI hA1Entry :
      ∀ _ : Fin 1, SigmaFinite (matrixEntryReferenceMeasure ρ ρ) := by
    intro _
    exact sigmaFinite_matrixEntryReferenceMeasure ρ ρ
  have hA1 :
      SigmaFinite (Measure.pi
        (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)) := by
    exact @MeasureTheory.Measure.pi.sigmaFinite
      (Fin 1) (fun _ : Fin 1 => Matrix ρ ρ ℝ) _ _
      (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ) hA1Entry
  haveI hF2Entry :
      ∀ p : Fin 2,
        SigmaFinite
          (matrixEntryReferenceMeasure ρ
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)) := by
    intro p
    exact sigmaFinite_matrixEntryReferenceMeasure ρ
      (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)
  have hF2 :
      SigmaFinite (Measure.pi
        (fun p : Fin 2 =>
          matrixEntryReferenceMeasure ρ
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))) := by
    exact @MeasureTheory.Measure.pi.sigmaFinite
      (Fin 2)
      (fun p : Fin 2 =>
        Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
      _ _
      (fun p : Fin 2 =>
        matrixEntryReferenceMeasure ρ
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))
      hF2Entry
  haveI hA3Entry :
      ∀ p : Fin 1,
        SigmaFinite
          (matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ) := by
    intro p
    exact sigmaFinite_matrixEntryReferenceMeasure
      (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ
  have hA3 :
      SigmaFinite (Measure.pi
        (fun p : Fin 1 =>
          matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)) := by
    exact @MeasureTheory.Measure.pi.sigmaFinite
      (Fin 1)
      (fun p : Fin 1 =>
        Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
      _ _
      (fun p : Fin 1 =>
        matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)
      hA3Entry
  have hCtop :
      SigmaFinite (matrixEntryReferenceMeasure ρ ρ) :=
    sigmaFinite_matrixEntryReferenceMeasure ρ ρ
  have hF3 :
      SigmaFinite
        (matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ) :=
    sigmaFinite_matrixEntryReferenceMeasure
      (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ
  have hCtopF3 :
      SigmaFinite
        ((matrixEntryReferenceMeasure ρ ρ).prod
          (matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ)) := by
    exact @MeasureTheory.Measure.prod.instSigmaFinite
      _ _ inferInstance (matrixEntryReferenceMeasure ρ ρ) hCtop
      inferInstance
      (matrixEntryReferenceMeasure
        (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ) hF3
  have hA3Tail :
      SigmaFinite
        ((Measure.pi
          (fun p : Fin 1 =>
            matrixEntryReferenceMeasure
              (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)).prod
          ((matrixEntryReferenceMeasure ρ ρ).prod
            (matrixEntryReferenceMeasure
              (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ))) := by
    exact @MeasureTheory.Measure.prod.instSigmaFinite
      _ _ inferInstance
      (Measure.pi
        (fun p : Fin 1 =>
          matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)) hA3
      inferInstance
      ((matrixEntryReferenceMeasure ρ ρ).prod
        (matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ)) hCtopF3
  have hF2Tail :
      SigmaFinite
        ((Measure.pi
          (fun p : Fin 2 =>
            matrixEntryReferenceMeasure ρ
              (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))).prod
          ((Measure.pi
            (fun p : Fin 1 =>
              matrixEntryReferenceMeasure
                (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)).prod
            ((matrixEntryReferenceMeasure ρ ρ).prod
              (matrixEntryReferenceMeasure
                (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ)))) := by
    exact @MeasureTheory.Measure.prod.instSigmaFinite
      _ _ inferInstance
      (Measure.pi
        (fun p : Fin 2 =>
          matrixEntryReferenceMeasure ρ
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))) hF2
      inferInstance
      ((Measure.pi
        (fun p : Fin 1 =>
          matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)).prod
        ((matrixEntryReferenceMeasure ρ ρ).prod
          (matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ))) hA3Tail
  exact @MeasureTheory.Measure.prod.instSigmaFinite
    _ _ inferInstance
    (Measure.pi (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)) hA1
    inferInstance
    ((Measure.pi
      (fun p : Fin 2 =>
        matrixEntryReferenceMeasure ρ
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))).prod
      ((Measure.pi
        (fun p : Fin 1 =>
          matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)).prod
        ((matrixEntryReferenceMeasure ρ ρ).prod
          (matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ)))) hF2Tail

set_option linter.style.longLine false in
/-- The coordinate-product reference measure on the passive fields is
s-finite. -/
theorem sFinite_case2PassiveThetaPassiveFieldReferenceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ) :
    SFinite
      (case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J) := by
  haveI :
      SigmaFinite
        (case2PassiveThetaPassiveFieldReferenceMeasure
          (ρ := ρ) (τ := τ) n S J) :=
    sigmaFinite_case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J
  infer_instance

set_option linter.style.longLine false in
/-- Selected-entry signed-box measure on the successor residual center
coordinates. -/
noncomputable def case2PassiveThetaCenterSignedBoxMeasure
    (n : ℕ → ℕ) {S J : ℕ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure (Case2PassiveTheta.Center n S J → ℝ) :=
  Measure.pi
    (fun i : Case2PassiveTheta.Center n S J =>
      volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))

set_option linter.style.longLine false in
/-- Weighted selected-entry signed-box measure on the successor residual
center coordinates. -/
noncomputable def case2PassiveThetaCenterWeightedBoxMeasure
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure (Case2PassiveTheta.Center n S J → ℝ) :=
  (case2PassiveThetaCenterSignedBoxMeasure n Rres).withDensity
    (fun y : Case2PassiveTheta.Center n S J → ℝ =>
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity
          (case2PassiveThetaPivotNext n hS hnext) y))

set_option linter.style.longLine false in
/-- Concrete passive-theta product reference measure: coordinate-product
Lebesgue reference on passive fields times the weighted selected-entry
signed-box reference on the residual center coordinates. -/
noncomputable def case2PassiveThetaReferenceSourceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
  (case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J).prod
    (case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres)

set_option linter.style.longLine false in
/-- The concrete passive-theta product reference measure is s-finite. -/
theorem sFinite_case2PassiveThetaReferenceSourceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    SFinite
      (case2PassiveThetaReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres) := by
  haveI :
      SFinite
        (case2PassiveThetaPassiveFieldReferenceMeasure
          (ρ := ρ) (τ := τ) n S J) :=
    sFinite_case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J
  dsimp [case2PassiveThetaReferenceSourceMeasure,
    case2PassiveThetaCenterWeightedBoxMeasure,
    case2PassiveThetaCenterSignedBoxMeasure]
  infer_instance

set_option linter.style.longLine false in
/-- Endpoint topology-tuple image measure of the concrete passive-theta
reference source restricted to a chosen local set.

This names the correct image-measure target for the current passive-theta
domain.  It is not unrestricted Haar on the full retained-passive determinant
chart. -/
noncomputable def case2PassiveThetaEndpointReferenceImageMeasure
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)) :
    Measure (TopologyTuple ρ κ' ℝ) :=
  let referenceSource :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  let Y :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  Measure.map Y (referenceSource.restrict Ω)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The concrete passive-theta reference source is supported on the
determinant chart after restricting to any measurable determinant-sector
localization.

This is support only.  It does not prove that the endpoint pushforward is Haar,
absolutely continuous with bounded density, or dominated by a determinant-chart
Haar measure. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩdet : Ω ⊆ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J) :
    let referenceSource :
        Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let Y :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let rawDetChart : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    (Measure.map Y (referenceSource.restrict Ω)).restrict rawDetChart =
      Measure.map Y (referenceSource.restrict Ω) := by
  intro referenceSource Y rawDetChart
  have hY :
      AEMeasurable Y (referenceSource.restrict Ω) := by
    have hYcont : Continuous Y := by
      simpa [Y] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  simpa [referenceSource, Y, rawDetChart] using
    measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_detChartSet_eq_self_of_subset_detSector
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
      referenceSource Ω hΩ hΩdet hY

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The named endpoint reference image measure is supported on the determinant
chart after determinant-sector localization.

This is the same support statement as
`measure_map_case2PassiveThetaEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector`,
but stated for the named image measure rather than an unfolded `Measure.map`.
It is not unrestricted determinant-chart Haar. -/
theorem case2PassiveThetaEndpointReferenceImageMeasure_restrict_detChartSet_eq_self_of_subset_detSector
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩdet : Ω ⊆ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J) :
    let endpointReferenceImage :
        Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    let rawDetChart : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    endpointReferenceImage.restrict rawDetChart = endpointReferenceImage := by
  intro endpointReferenceImage rawDetChart
  simpa [endpointReferenceImage, rawDetChart,
    case2PassiveThetaEndpointReferenceImageMeasure] using
    measure_map_case2PassiveThetaEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω hΩ hΩdet

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Passive-field domination by the concrete coordinate reference pushes
forward to domination by the named endpoint reference image measure.

This is the honest replacement for an unrestricted determinant-chart Haar
target at the passive-theta level.  It assumes only domain-side passive-field
domination and concludes domination by the actual endpoint image measure of
the concrete reference source. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_passiveSource_restrict_le_smul_endpointReferenceImage_of_passiveMeasure_le_smul_reference
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (passiveMeasure :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
    {d : ℝ≥0∞}
    (hpassive :
      passiveMeasure ≤
        d • case2PassiveThetaPassiveFieldReferenceMeasure
          (ρ := ρ) (τ := τ) n S J) :
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres
    let passiveSource :
        Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let endpointReferenceImage :
        Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    let Y :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    Measure.map Y (passiveSource.restrict Ω) ≤ d • endpointReferenceImage := by
  intro weightedBox passiveSource endpointReferenceImage Y
  let referencePassive :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J
  let referenceSource :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    referencePassive.prod weightedBox
  haveI : SFinite weightedBox := by
    subst weightedBox
    dsimp [case2PassiveThetaCenterWeightedBoxMeasure,
      case2PassiveThetaCenterSignedBoxMeasure]
    infer_instance
  have hprod : passiveSource ≤ d • referenceSource := by
    change passiveMeasure.prod weightedBox ≤ d • referencePassive.prod weightedBox
    exact prod_le_smul_prod_of_le_smul_left (η := weightedBox) hpassive
  have hrestrict :
      passiveSource.restrict Ω ≤ d • referenceSource.restrict Ω := by
    calc
      passiveSource.restrict Ω ≤ (d • referenceSource).restrict Ω :=
        Measure.restrict_mono Set.Subset.rfl hprod
      _ = d • referenceSource.restrict Ω := by
        rw [Measure.restrict_smul]
  have hY :
      AEMeasurable Y (referenceSource.restrict Ω) := by
    have hYcont : Continuous Y := by
      simpa [Y] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hmap :
      Measure.map Y (passiveSource.restrict Ω) ≤
        d • Measure.map Y (referenceSource.restrict Ω) :=
    map_le_smul_map_of_le_smul_aemeasurable hY hrestrict
  simpa [endpointReferenceImage, case2PassiveThetaEndpointReferenceImageMeasure,
    referenceSource, referencePassive, weightedBox, Y] using hmap

end Aoyagi
end DLN
end DLNFibre
