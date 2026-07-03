import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

set_option linter.style.longLine false in
/-- Product types inherit measurable additive translations from their two
factors.  This local constructor keeps the Aoyagi coordinate-product Haar
proofs explicit where Mathlib has no direct instance available at this pin. -/
theorem measurableAdd_prod_of_measurableAdd
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Add α] [Add β] [MeasurableAdd α] [MeasurableAdd β] :
    MeasurableAdd (α × β) where
  measurable_const_add c := by
    change Measurable (fun x : α × β => (c.1 + x.1, c.2 + x.2))
    exact ((measurable_const_add c.1).comp measurable_fst).prod
      ((measurable_const_add c.2).comp measurable_snd)
  measurable_add_const c := by
    change Measurable (fun x : α × β => (x.1 + c.1, x.2 + c.2))
    exact ((measurable_add_const c.1).comp measurable_fst).prod
      ((measurable_add_const c.2).comp measurable_snd)

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

set_option linter.style.longLine false in
/-- The full coordinate-product reference measure on a finite real matrix
space is additive Haar. -/
theorem isAddHaarMeasure_matrixEntryReferenceMeasure
    (m n : Type*) [Fintype m] [Fintype n] :
    (matrixEntryReferenceMeasure m n).IsAddHaarMeasure := by
  change
    (Measure.pi fun _ : m =>
      Measure.pi fun _ : n => (volume : Measure ℝ)).IsAddHaarMeasure
  haveI hrow :
      ∀ _ : m,
        (Measure.pi fun _ : n => (volume : Measure ℝ)).IsAddHaarMeasure := by
    intro _
    simpa [volume_pi] using (isAddHaarMeasure_volume_pi n)
  exact
    Measure.pi.isAddHaarMeasure
      (fun _ : m => Measure.pi fun _ : n => (volume : Measure ℝ))

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

/-- Dependent finite Pi-box of matrix-entry boxes. -/
def piMatrixEntryBox
    {ι : Type*} {r c : ι → Type*}
    (F₀ : ∀ i : ι, Matrix (r i) (c i) ℝ) (R : ℝ) :
    Set (∀ i : ι, Matrix (r i) (c i) ℝ) :=
  {F | ∀ i, F i ∈ matrixEntryBox (F₀ i) R}

theorem mem_piMatrixEntryBox_self
    {ι : Type*} {r c : ι → Type*}
    (F₀ : ∀ i : ι, Matrix (r i) (c i) ℝ) {R : ℝ} (hR : 0 < R) :
    F₀ ∈ piMatrixEntryBox F₀ R := by
  intro i
  exact mem_matrixEntryBox_self (F₀ i) hR

set_option linter.unusedFintypeInType false in
theorem isOpen_piMatrixEntryBox
    {ι : Type*} [Fintype ι] {r c : ι → Type*}
    [∀ i, Fintype (r i)] [∀ i, Fintype (c i)]
    (F₀ : ∀ i : ι, Matrix (r i) (c i) ℝ) (R : ℝ) :
    IsOpen (piMatrixEntryBox F₀ R) := by
  classical
  have hbox :
      piMatrixEntryBox F₀ R =
        Set.pi Set.univ (fun i : ι => matrixEntryBox (F₀ i) R) := by
    ext F
    constructor
    · intro hF i _
      exact hF i
    · intro hF i
      exact hF i (Set.mem_univ i)
  rw [hbox]
  exact isOpen_set_pi Set.finite_univ fun i _ =>
    isOpen_matrixEntryBox (F₀ i) R

set_option linter.unusedFintypeInType false in
theorem measurableSet_piMatrixEntryBox
    {ι : Type*} [Fintype ι] {r c : ι → Type*}
    [∀ i, Fintype (r i)] [∀ i, Fintype (c i)]
    (F₀ : ∀ i : ι, Matrix (r i) (c i) ℝ) (R : ℝ) :
    MeasurableSet (piMatrixEntryBox F₀ R) := by
  classical
  have hbox :
      piMatrixEntryBox F₀ R =
        Set.pi Set.univ (fun i : ι => matrixEntryBox (F₀ i) R) := by
    ext F
    constructor
    · intro hF i _
      exact hF i
    · intro hF i
      exact hF i (Set.mem_univ i)
  rw [hbox]
  exact MeasurableSet.univ_pi fun i =>
    measurableSet_matrixEntryBox (F₀ i) R

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
theorem piMatrixEntryReferenceMeasure_piMatrixEntryBox_lt_top
    {ι : Type*} [Fintype ι] {r c : ι → Type*}
    [∀ i, Fintype (r i)] [∀ i, Fintype (c i)]
    (F₀ : ∀ i : ι, Matrix (r i) (c i) ℝ) (R : ℝ) :
    (Measure.pi fun i : ι => matrixEntryReferenceMeasure (r i) (c i))
      (piMatrixEntryBox F₀ R) < ∞ := by
  classical
  have hbox :
      piMatrixEntryBox F₀ R =
        Set.pi Set.univ (fun i : ι => matrixEntryBox (F₀ i) R) := by
    ext F
    constructor
    · intro hF i _
      exact hF i
    · intro hF i
      exact hF i (Set.mem_univ i)
  haveI :
      ∀ i : ι, SigmaFinite (matrixEntryReferenceMeasure (r i) (c i)) :=
    fun i => sigmaFinite_matrixEntryReferenceMeasure (r i) (c i)
  rw [hbox, Measure.pi_pi]
  exact ENNReal.prod_lt_top fun i _ =>
    matrixEntryReferenceMeasure_matrixEntryBox_lt_top (F₀ i) R

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
set_option linter.unusedFintypeInType false in
/-- The passive-field coordinate product has measurable additive
translations. -/
theorem measurableAdd_case2PassiveThetaPassiveFields
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ) :
    MeasurableAdd
      (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) := by
  change
    MeasurableAdd
      ((Fin 1 → Matrix ρ ρ ℝ) ×
        ((∀ p : Fin 2,
          Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ) ×
          ((∀ p : Fin 1,
            Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) ×
            (Matrix ρ ρ ℝ ×
              Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ))))
  haveI hCtopF3Meas :
      MeasurableAdd
        (Matrix ρ ρ ℝ ×
          Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ) :=
    measurableAdd_prod_of_measurableAdd
  haveI hA3RestMeas :
      MeasurableAdd
        ((∀ p : Fin 1,
          Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) ×
          (Matrix ρ ρ ℝ ×
            Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)) :=
    measurableAdd_prod_of_measurableAdd
  haveI hF2RestMeas :
      MeasurableAdd
        ((∀ p : Fin 2,
          Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ) ×
          ((∀ p : Fin 1,
            Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) ×
            (Matrix ρ ρ ℝ ×
              Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ))) :=
    measurableAdd_prod_of_measurableAdd
  exact measurableAdd_prod_of_measurableAdd

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
/-- The full coordinate-product reference measure on the passive fields is
additive Haar. -/
theorem isAddHaarMeasure_case2PassiveThetaPassiveFieldReferenceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ) :
    (case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J).IsAddHaarMeasure := by
  dsimp [case2PassiveThetaPassiveFieldReferenceMeasure]
  haveI hA1 :
      (Measure.pi
        (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)).IsAddHaarMeasure := by
    let μ : Fin 1 → Measure (Matrix ρ ρ ℝ) :=
      fun _ => matrixEntryReferenceMeasure ρ ρ
    have hsigma : ∀ i : Fin 1, SigmaFinite (μ i) := by
      intro _
      exact sigmaFinite_matrixEntryReferenceMeasure ρ ρ
    have hhaar : ∀ i : Fin 1, (μ i).IsAddHaarMeasure := by
      intro _
      exact isAddHaarMeasure_matrixEntryReferenceMeasure ρ ρ
    exact
      @Measure.pi.isAddHaarMeasure
        (Fin 1) (fun _ : Fin 1 => Matrix ρ ρ ℝ) _ _ μ hsigma _ _ hhaar _
  haveI hA1SF :
      SFinite (Measure.pi
        (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)) := by
    haveI hA1Sigma :
        SigmaFinite (Measure.pi
          (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)) := by
      have hsigma :
          ∀ i : Fin 1,
            SigmaFinite ((fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ) i) := by
        intro _
        exact sigmaFinite_matrixEntryReferenceMeasure ρ ρ
      exact
        @Measure.pi.sigmaFinite
          (Fin 1) (fun _ : Fin 1 => Matrix ρ ρ ℝ) _ _
          (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ) hsigma
    infer_instance
  haveI hF2 :
      (Measure.pi
        (fun p : Fin 2 =>
          matrixEntryReferenceMeasure ρ
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))).IsAddHaarMeasure := by
    let μ : (p : Fin 2) →
        Measure (Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ) :=
      fun p =>
        matrixEntryReferenceMeasure ρ
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)
    have hsigma : ∀ p : Fin 2, SigmaFinite (μ p) := by
      intro p
      exact sigmaFinite_matrixEntryReferenceMeasure ρ
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)
    have hhaar : ∀ p : Fin 2, (μ p).IsAddHaarMeasure := by
      intro p
      exact isAddHaarMeasure_matrixEntryReferenceMeasure ρ
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)
    exact
      @Measure.pi.isAddHaarMeasure
        (Fin 2)
        (fun p : Fin 2 =>
          Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
        _ _ μ hsigma _ _ hhaar _
  haveI hF2SF :
      SFinite (Measure.pi
        (fun p : Fin 2 =>
          matrixEntryReferenceMeasure ρ
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))) := by
    haveI hF2Sigma :
        SigmaFinite (Measure.pi
          (fun p : Fin 2 =>
            matrixEntryReferenceMeasure ρ
              (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))) := by
      have hsigma :
          ∀ p : Fin 2,
            SigmaFinite
              ((fun p : Fin 2 =>
                matrixEntryReferenceMeasure ρ
                  (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)) p) := by
        intro p
        exact sigmaFinite_matrixEntryReferenceMeasure ρ
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)
      exact
        @Measure.pi.sigmaFinite
          (Fin 2)
          (fun p : Fin 2 =>
            Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
          _ _
          (fun p : Fin 2 =>
            matrixEntryReferenceMeasure ρ
              (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)) hsigma
    infer_instance
  haveI hA3 :
      (Measure.pi
        (fun p : Fin 1 =>
          matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)).IsAddHaarMeasure := by
    let μ : (p : Fin 1) →
        Measure (Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) :=
      fun p =>
        matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ
    have hsigma : ∀ p : Fin 1, SigmaFinite (μ p) := by
      intro p
      exact sigmaFinite_matrixEntryReferenceMeasure
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ
    have hhaar : ∀ p : Fin 1, (μ p).IsAddHaarMeasure := by
      intro p
      exact isAddHaarMeasure_matrixEntryReferenceMeasure
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ
    exact
      @Measure.pi.isAddHaarMeasure
        (Fin 1)
        (fun p : Fin 1 =>
          Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
        _ _ μ hsigma _ _ hhaar _
  haveI hA3SF :
      SFinite (Measure.pi
        (fun p : Fin 1 =>
          matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)) := by
    haveI hA3Sigma :
        SigmaFinite (Measure.pi
          (fun p : Fin 1 =>
            matrixEntryReferenceMeasure
              (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)) := by
      have hsigma :
          ∀ p : Fin 1,
            SigmaFinite
              ((fun p : Fin 1 =>
                matrixEntryReferenceMeasure
                  (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ) p) := by
        intro p
        exact sigmaFinite_matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ
      exact
        @Measure.pi.sigmaFinite
          (Fin 1)
          (fun p : Fin 1 =>
            Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
          _ _
          (fun p : Fin 1 =>
            matrixEntryReferenceMeasure
              (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ) hsigma
    infer_instance
  haveI hCtop : (matrixEntryReferenceMeasure ρ ρ).IsAddHaarMeasure :=
    isAddHaarMeasure_matrixEntryReferenceMeasure ρ ρ
  haveI hCtopSF : SFinite (matrixEntryReferenceMeasure ρ ρ) :=
    sFinite_matrixEntryReferenceMeasure ρ ρ
  haveI hF3 :
      (matrixEntryReferenceMeasure
        (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ).IsAddHaarMeasure :=
    isAddHaarMeasure_matrixEntryReferenceMeasure
      (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ
  haveI hF3SF :
      SFinite
        (matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ) :=
    sFinite_matrixEntryReferenceMeasure
      (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ
  let A1Measure : Measure (Fin 1 → Matrix ρ ρ ℝ) :=
    Measure.pi (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)
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
  change
    (A1Measure.prod
      (F2Measure.prod (A3Measure.prod (CtopMeasure.prod F3Measure)))).IsAddHaarMeasure
  haveI : A1Measure.IsAddHaarMeasure := by
    dsimp [A1Measure]
    infer_instance
  haveI : SFinite A1Measure := by
    dsimp [A1Measure]
    infer_instance
  haveI : F2Measure.IsAddHaarMeasure := by
    dsimp [F2Measure]
    infer_instance
  haveI : SFinite F2Measure := by
    dsimp [F2Measure]
    infer_instance
  haveI : A3Measure.IsAddHaarMeasure := by
    dsimp [A3Measure]
    infer_instance
  haveI : SFinite A3Measure := by
    dsimp [A3Measure]
    infer_instance
  haveI : CtopMeasure.IsAddHaarMeasure := by
    exact hCtop
  haveI : SFinite CtopMeasure := by
    exact hCtopSF
  haveI : F3Measure.IsAddHaarMeasure := by
    exact hF3
  haveI : SFinite F3Measure := by
    exact hF3SF
  haveI hCtopF3H : (CtopMeasure.prod F3Measure).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure CtopMeasure F3Measure
  haveI hCtopF3SF : SFinite (CtopMeasure.prod F3Measure) :=
    Measure.prod.instSFinite
  haveI hCtopF3Meas :
      MeasurableAdd
        (Matrix ρ ρ ℝ ×
          Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ) :=
    measurableAdd_prod_of_measurableAdd
  haveI hA3RestH :
      (A3Measure.prod (CtopMeasure.prod F3Measure)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure A3Measure (CtopMeasure.prod F3Measure)
  haveI hA3RestSF :
      SFinite (A3Measure.prod (CtopMeasure.prod F3Measure)) :=
    Measure.prod.instSFinite
  haveI hA3RestMeas :
      MeasurableAdd
        ((∀ p : Fin 1,
          Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) ×
          (Matrix ρ ρ ℝ ×
            Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)) :=
    measurableAdd_prod_of_measurableAdd
  haveI hF2RestH :
      (F2Measure.prod (A3Measure.prod (CtopMeasure.prod F3Measure))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure F2Measure
      (A3Measure.prod (CtopMeasure.prod F3Measure))
  haveI hF2RestSF :
      SFinite (F2Measure.prod (A3Measure.prod (CtopMeasure.prod F3Measure))) :=
    Measure.prod.instSFinite
  haveI hF2RestMeas :
      MeasurableAdd
        ((∀ p : Fin 2,
          Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ) ×
        ((∀ p : Fin 1,
          Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) ×
          (Matrix ρ ρ ℝ ×
            Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ))) :=
    measurableAdd_prod_of_measurableAdd
  exact
    Measure.prod.instIsAddHaarMeasure A1Measure
      (F2Measure.prod (A3Measure.prod (CtopMeasure.prod F3Measure)))

set_option linter.style.longLine false in
/-- Entrywise product box around all passive Case 2 fields.  This is a
coordinate-reference local set only; it is not an original-prior or Haar
localization. -/
def case2PassiveThetaPassiveFieldBox
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ)
    (theta0 : Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)
    (R : ℝ) :
    Set (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
  (piMatrixEntryBox theta0.1 R) ×ˢ
    ((piMatrixEntryBox theta0.2.1 R) ×ˢ
      ((piMatrixEntryBox theta0.2.2.1 R) ×ˢ
        ((matrixEntryBox theta0.2.2.2.1 R) ×ˢ
          (matrixEntryBox theta0.2.2.2.2 R))))

set_option linter.style.longLine false in
theorem mem_case2PassiveThetaPassiveFieldBox_self
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ)
    (theta0 : Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)
    {R : ℝ} (hR : 0 < R) :
    theta0 ∈ case2PassiveThetaPassiveFieldBox n S J theta0 R := by
  exact
    ⟨mem_piMatrixEntryBox_self theta0.1 hR,
      mem_piMatrixEntryBox_self theta0.2.1 hR,
      mem_piMatrixEntryBox_self theta0.2.2.1 hR,
      mem_matrixEntryBox_self theta0.2.2.2.1 hR,
      mem_matrixEntryBox_self theta0.2.2.2.2 hR⟩

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
theorem isOpen_case2PassiveThetaPassiveFieldBox
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ)
    (theta0 : Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)
    (R : ℝ) :
    IsOpen (case2PassiveThetaPassiveFieldBox n S J theta0 R) := by
  exact
    (isOpen_piMatrixEntryBox theta0.1 R).prod
      ((isOpen_piMatrixEntryBox theta0.2.1 R).prod
        ((isOpen_piMatrixEntryBox theta0.2.2.1 R).prod
          ((isOpen_matrixEntryBox theta0.2.2.2.1 R).prod
            (isOpen_matrixEntryBox theta0.2.2.2.2 R))))

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
theorem measurableSet_case2PassiveThetaPassiveFieldBox
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ)
    (theta0 : Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)
    (R : ℝ) :
    MeasurableSet (case2PassiveThetaPassiveFieldBox n S J theta0 R) := by
  exact
    (measurableSet_piMatrixEntryBox theta0.1 R).prod
      ((measurableSet_piMatrixEntryBox theta0.2.1 R).prod
        ((measurableSet_piMatrixEntryBox theta0.2.2.1 R).prod
          ((measurableSet_matrixEntryBox theta0.2.2.2.1 R).prod
            (measurableSet_matrixEntryBox theta0.2.2.2.2 R))))

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
theorem case2PassiveThetaPassiveFieldReferenceMeasure_box_lt_top
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ)
    (theta0 : Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)
    (R : ℝ) :
    case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J
        (case2PassiveThetaPassiveFieldBox n S J theta0 R) < ∞ := by
  classical
  let A1Set : Set (Fin 1 → Matrix ρ ρ ℝ) :=
    piMatrixEntryBox theta0.1 R
  let F2Set :
      Set
        (∀ p : Fin 2,
          Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ) :=
    piMatrixEntryBox theta0.2.1 R
  let A3Set :
      Set
        (∀ p : Fin 1,
          Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) :=
    piMatrixEntryBox theta0.2.2.1 R
  let CtopSet : Set (Matrix ρ ρ ℝ) :=
    matrixEntryBox theta0.2.2.2.1 R
  let F3Set :
      Set
        (Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ) :=
    matrixEntryBox theta0.2.2.2.2 R
  have hA1_lt :
      (Measure.pi fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ) A1Set < ∞ := by
    simpa [A1Set] using
      piMatrixEntryReferenceMeasure_piMatrixEntryBox_lt_top theta0.1 R
  have hF2_lt :
      (Measure.pi
        (fun p : Fin 2 =>
          matrixEntryReferenceMeasure ρ
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))) F2Set < ∞ := by
    simpa [F2Set] using
      piMatrixEntryReferenceMeasure_piMatrixEntryBox_lt_top theta0.2.1 R
  have hA3_lt :
      (Measure.pi
        (fun p : Fin 1 =>
          matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)) A3Set < ∞ := by
    simpa [A3Set] using
      piMatrixEntryReferenceMeasure_piMatrixEntryBox_lt_top theta0.2.2.1 R
  have hCtop_lt :
      matrixEntryReferenceMeasure ρ ρ CtopSet < ∞ := by
    simpa [CtopSet] using
      matrixEntryReferenceMeasure_matrixEntryBox_lt_top theta0.2.2.2.1 R
  have hF3_lt :
      matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ F3Set < ∞ := by
    simpa [F3Set] using
      matrixEntryReferenceMeasure_matrixEntryBox_lt_top theta0.2.2.2.2 R
  have hCtopF3_lt :
      ((matrixEntryReferenceMeasure ρ ρ).prod
        (matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ))
          (CtopSet ×ˢ F3Set) < ∞ :=
    lt_of_le_of_lt (Measure.prod_prod_le CtopSet F3Set)
      (ENNReal.mul_lt_top hCtop_lt hF3_lt)
  have hA3Tail_lt :
      ((Measure.pi
        (fun p : Fin 1 =>
          matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)).prod
        ((matrixEntryReferenceMeasure ρ ρ).prod
          (matrixEntryReferenceMeasure
            (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ)))
          (A3Set ×ˢ (CtopSet ×ˢ F3Set)) < ∞ :=
    lt_of_le_of_lt (Measure.prod_prod_le A3Set (CtopSet ×ˢ F3Set))
      (ENNReal.mul_lt_top hA3_lt hCtopF3_lt)
  have hF2Tail_lt :
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
              (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ))))
          (F2Set ×ˢ (A3Set ×ˢ (CtopSet ×ˢ F3Set))) < ∞ :=
    lt_of_le_of_lt
      (Measure.prod_prod_le F2Set (A3Set ×ˢ (CtopSet ×ˢ F3Set)))
      (ENNReal.mul_lt_top hF2_lt hA3Tail_lt)
  have hA1Tail_lt :
      ((Measure.pi (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)).prod
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
                (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ)))))
          (A1Set ×ˢ (F2Set ×ˢ (A3Set ×ˢ (CtopSet ×ˢ F3Set)))) < ∞ :=
    lt_of_le_of_lt
      (Measure.prod_prod_le A1Set (F2Set ×ˢ (A3Set ×ˢ (CtopSet ×ˢ F3Set))))
      (ENNReal.mul_lt_top hA1_lt hF2Tail_lt)
  simpa [case2PassiveThetaPassiveFieldReferenceMeasure,
    case2PassiveThetaPassiveFieldBox, A1Set, F2Set, A3Set, CtopSet, F3Set]
    using hA1Tail_lt

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
/-- A finite open self-restriction of the passive-field coordinate reference
measure around any passive-field point.

The witness is an entrywise coordinate-product box and the comparison is the
identity domination of the restricted reference measure by itself with scalar
`1`.  This proves no original-prior, determinant-Haar, raw-Haar, density,
normal-crossing, pole-order, or RLCT statement. -/
theorem exists_open_passiveLocalSet_case2PassiveThetaPassiveFieldReferenceMeasure_restrict_self_le_smul
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ)
    (theta0 : Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :
    let passiveRef :=
      case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J
    ∃ passiveLocalSet :
        Set (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J),
    ∃ passiveMeasure :
        Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J),
    ∃ Cpassive : ℝ≥0∞,
      theta0 ∈ passiveLocalSet ∧
        IsOpen passiveLocalSet ∧
        MeasurableSet passiveLocalSet ∧
        passiveMeasure = passiveRef.restrict passiveLocalSet ∧
        passiveMeasure Set.univ < ∞ ∧
        Cpassive = 1 ∧
        Cpassive < ∞ ∧
        passiveRef.restrict passiveLocalSet ≤ Cpassive • passiveMeasure := by
  intro passiveRef
  let passiveLocalSet :=
    case2PassiveThetaPassiveFieldBox (ρ := ρ) (τ := τ) n S J theta0 1
  let passiveMeasure : Measure
      (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
    passiveRef.restrict passiveLocalSet
  let Cpassive : ℝ≥0∞ := 1
  have hmem : theta0 ∈ passiveLocalSet := by
    simpa [passiveLocalSet] using
      mem_case2PassiveThetaPassiveFieldBox_self n S J theta0 zero_lt_one
  have hopen : IsOpen passiveLocalSet := by
    simpa [passiveLocalSet] using
      isOpen_case2PassiveThetaPassiveFieldBox n S J theta0 1
  have hmeas : MeasurableSet passiveLocalSet := by
    simpa [passiveLocalSet] using
      measurableSet_case2PassiveThetaPassiveFieldBox n S J theta0 1
  have hlt_top : passiveMeasure Set.univ < ∞ := by
    simpa [passiveMeasure, passiveLocalSet, passiveRef] using
      case2PassiveThetaPassiveFieldReferenceMeasure_box_lt_top
        (ρ := ρ) (τ := τ) n S J theta0 1
  refine
    ⟨passiveLocalSet, passiveMeasure, Cpassive, hmem, hopen, hmeas, rfl,
      hlt_top, rfl, ENNReal.one_lt_top, ?_⟩
  simp [Cpassive, passiveMeasure]

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
