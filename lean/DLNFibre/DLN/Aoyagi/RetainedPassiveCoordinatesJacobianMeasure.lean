import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesMeasure

/-!
# Retained-passive raw-order measure identities with computed Jacobian density

This file specializes the retained-passive raw-order change-of-variables
theorem by replacing the abstract forward density `|det D raw|` with the
point-specialized formal determinant, and with its solved-`A1` product formula,
on the determinant chart.  It is still a local chart measure identity: it does
not construct an original-source prior, prove normal crossings, compute a pole
order, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.Operator Topology

namespace DLNFibre
namespace DLN
namespace Aoyagi
namespace ChartLocalSuffixState
namespace RetainedPassiveNonredundantCoordinateData

set_option linter.style.longLine false in
/-- The solved-`A1` product formula for the formal retained-passive raw-order
absolute determinant. -/
def retainedPassiveFormalRawOrderJacobianProductAbsDetAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) : ℝ :=
  let data :
      RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) κ' :=
    ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord :
      RetainedPassiveCoordinateData
        (K := ℝ) (ρ := ρ) κ' :=
    data.toCoordinateData
  |((retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed)⁻¹).det| ^ Fintype.card ρ *
    (∏ p : Fin (M + 1),
      |(coord.solvedA1 p).det| ^ Fintype.card (κ' p.castSucc)) *
      |(coord.solvedA1 (Fin.last M)).det| ^
        Fintype.card (κ' (Fin.last (M + 1)))

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- On the retained-passive determinant chart, the solved-`A1` product density
is the actual forward raw-order Frechet absolute determinant. -/
theorem retainedPassiveFormalRawOrderJacobianProductAbsDetAt_eq_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    retainedPassiveFormalRawOrderJacobianProductAbsDetAt
        (M := M) (ρ := ρ) (κ' := κ') z =
      topologyTupleEdgeRawOrderFDerivAbsDet
        (M := M) (ρ := ρ) (κ' := κ') z := by
  cases M with
  | zero =>
      have hdet :
          topologyTupleEdgeRawOrderFDerivAbsDet
              (M := 0) (ρ := ρ) (κ' := κ') z =
            retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := 0) (ρ := ρ) (κ' := κ') z := by
        simpa [retainedPassiveFormalRawOrderJacobianProductAbsDetAt] using
          Aoyagi.topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_zeroTail
            (ρ := ρ) (κ' := κ') hz
      exact hdet.symm
  | succ M =>
      have hdet :
          topologyTupleEdgeRawOrderFDerivAbsDet
              (M := M + 1) (ρ := ρ) (κ' := κ') z =
            retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M + 1) (ρ := ρ) (κ' := κ') z := by
        simpa [Nat.succ_eq_add_one, retainedPassiveFormalRawOrderJacobianProductAbsDetAt] using
          Aoyagi.topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_posTail
            (M := M) (ρ := ρ) (κ' := κ') hz
      exact hdet.symm

set_option linter.style.longLine false in
/-- The solved-`A1` product determinant density is positive on the
retained-passive determinant chart. -/
theorem retainedPassiveFormalRawOrderJacobianProductAbsDetAt_pos_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    0 <
      retainedPassiveFormalRawOrderJacobianProductAbsDetAt
        (M := M) (ρ := ρ) (κ' := κ') z := by
  rw [
    retainedPassiveFormalRawOrderJacobianProductAbsDetAt_eq_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
      (M := M) (ρ := ρ) (κ' := κ') hz]
  exact
    topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') hz

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The solved-`A1` product determinant density is continuous at
retained-passive determinant-chart points. -/
theorem continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContinuousAt
      (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
        (M := M) (ρ := ρ) (κ' := κ')) z₀ := by
  have hactual :
      ContinuousAt
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (M := M) (ρ := ρ) (κ' := κ')) z₀ :=
    continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z₀ hz₀
  have heq :
      (topologyTupleEdgeRawOrderFDerivAbsDet
          (M := M) (ρ := ρ) (κ' := κ')) =ᶠ[𝓝 z₀]
        retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') := by
    filter_upwards [
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).mem_nhds hz₀] with z hz
    exact
      (retainedPassiveFormalRawOrderJacobianProductAbsDetAt_eq_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
        (M := M) (ρ := ρ) (κ' := κ') hz).symm
  exact hactual.congr heq

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Near any retained-passive determinant-chart point, the solved-`A1` product
determinant density admits a positive local lower bound. -/
theorem exists_pos_eventually_le_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_nhds
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ z in 𝓝 z₀,
        ε ≤ retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') z := by
  rcases exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds
      (ρ := ρ) (κ' := κ') z₀ hz₀ with
    ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  filter_upwards [
    hε,
    (isOpen_topologyTupleDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')).mem_nhds hz₀] with z hz_low hz
  rw [
    retainedPassiveFormalRawOrderJacobianProductAbsDetAt_eq_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
      (M := M) (ρ := ρ) (κ' := κ') hz]
  exact hz_low

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Near any retained-passive determinant-chart point, the solved-`A1` product
determinant density admits a positive local upper bound. -/
theorem exists_pos_eventually_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_le_nhds
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ z in 𝓝 z₀,
        retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') z ≤ K := by
  rcases exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds
      (ρ := ρ) (κ' := κ') z₀ hz₀ with
    ⟨K, hK_pos, hK⟩
  refine ⟨K, hK_pos, ?_⟩
  filter_upwards [
    hK,
    (isOpen_topologyTupleDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')).mem_nhds hz₀] with z hz_high hz
  rw [
    retainedPassiveFormalRawOrderJacobianProductAbsDetAt_eq_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
      (M := M) (ρ := ρ) (κ' := κ') hz]
  exact hz_high

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The solved-`A1` product determinant density is a positive bounded unit
after any source parametrization continuous at a point mapping into the
retained-passive determinant chart. -/
theorem exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_comp
    {α : Type*} [TopologicalSpace α]
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {Y : α → TopologyTuple ρ κ' ℝ} {a₀ : α}
    (hY : ContinuousAt Y a₀)
    (hY₀ : Y a₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∀ᶠ a in 𝓝 a₀,
        ε ≤ retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := M) (ρ := ρ) (κ' := κ') (Y a) ∧
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := M) (ρ := ρ) (κ' := κ') (Y a) ≤ K := by
  rcases exists_pos_eventually_le_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_nhds
      (ρ := ρ) (κ' := κ') (Y a₀) hY₀ with
    ⟨ε, hε_pos, hε⟩
  rcases exists_pos_eventually_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_le_nhds
      (ρ := ρ) (κ' := κ') (Y a₀) hY₀ with
    ⟨K, hK_pos, hK⟩
  refine ⟨ε, K, hε_pos, hK_pos, ?_⟩
  filter_upwards [hY.eventually hε, hY.eventually hK] with a ha_low ha_high
  exact ⟨ha_low, ha_high⟩

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Positive-tail retained-passive raw-order change of variables with formal
raw-order determinant density instead of the abstract Frechet determinant
density. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_posTail
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
                (M := M + 1) (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Factual : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z)
  let Fformal : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
          (M := M + 1) (ρ := ρ) (κ' := κ') z)
  have hEq : Fformal =ᵐ[m.restrict S] Factual := by
    filter_upwards [ae_restrict_mem₀ hs] with z hz
    have hdet :=
      Aoyagi.topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_posTail
        (M := M) (ρ := ρ) (κ' := κ') hz
    exact congrArg ENNReal.ofReal hdet.symm
  calc
    Measure.map Φ ((m.restrict S).withDensity Fformal) =
        Measure.map Φ ((m.restrict S).withDensity Factual) := by
          rw [withDensity_congr_ae hEq]
    _ = m.restrict T := by
          simpa [S, T, Φ, Factual] using
            map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
              (ρ := ρ) (κ' := κ') m hs

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Zero-tail retained-passive raw-order change of variables with formal
raw-order determinant density instead of the abstract Frechet determinant
density. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_zeroTail
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
                (M := 0) (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Factual : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z)
  let Fformal : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
          (M := 0) (ρ := ρ) (κ' := κ') z)
  have hEq : Fformal =ᵐ[m.restrict S] Factual := by
    filter_upwards [ae_restrict_mem₀ hs] with z hz
    have hdet :=
      Aoyagi.topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_zeroTail
        (ρ := ρ) (κ' := κ') hz
    exact congrArg ENNReal.ofReal hdet.symm
  calc
    Measure.map Φ ((m.restrict S).withDensity Fformal) =
        Measure.map Φ ((m.restrict S).withDensity Factual) := by
          rw [withDensity_congr_ae hEq]
    _ = m.restrict T := by
          simpa [S, T, Φ, Factual] using
            map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
              (ρ := ρ) (κ' := κ') m hs

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Positive-tail retained-passive raw-order change of variables with the
solved-`A1` product determinant density. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_posTail
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M + 1) (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Factual : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z)
  let Fproduct : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := M + 1) (ρ := ρ) (κ' := κ') z)
  have hEq : Fproduct =ᵐ[m.restrict S] Factual := by
    filter_upwards [ae_restrict_mem₀ hs] with z hz
    have hdet :
        topologyTupleEdgeRawOrderFDerivAbsDet
            (M := M + 1) (ρ := ρ) (κ' := κ') z =
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := M + 1) (ρ := ρ) (κ' := κ') z := by
      simpa [retainedPassiveFormalRawOrderJacobianProductAbsDetAt] using
        Aoyagi.topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_posTail
          (M := M) (ρ := ρ) (κ' := κ') hz
    exact congrArg ENNReal.ofReal hdet.symm
  calc
    Measure.map Φ ((m.restrict S).withDensity Fproduct) =
        Measure.map Φ ((m.restrict S).withDensity Factual) := by
          rw [withDensity_congr_ae hEq]
    _ = m.restrict T := by
          simpa [S, T, Φ, Factual] using
            map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
              (ρ := ρ) (κ' := κ') m hs

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Zero-tail retained-passive raw-order change of variables with the
solved-`A1` product determinant density. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_zeroTail
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := 0) (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Factual : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z)
  let Fproduct : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := 0) (ρ := ρ) (κ' := κ') z)
  have hEq : Fproduct =ᵐ[m.restrict S] Factual := by
    filter_upwards [ae_restrict_mem₀ hs] with z hz
    have hdet :
        topologyTupleEdgeRawOrderFDerivAbsDet
            (M := 0) (ρ := ρ) (κ' := κ') z =
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 0) (ρ := ρ) (κ' := κ') z := by
      simpa [retainedPassiveFormalRawOrderJacobianProductAbsDetAt] using
        Aoyagi.topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_zeroTail
          (ρ := ρ) (κ' := κ') hz
    exact congrArg ENNReal.ofReal hdet.symm
  calc
    Measure.map Φ ((m.restrict S).withDensity Fproduct) =
        Measure.map Φ ((m.restrict S).withDensity Factual) := by
          rw [withDensity_congr_ae hEq]
    _ = m.restrict T := by
          simpa [S, T, Φ, Factual] using
            map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
              (ρ := ρ) (κ' := κ') m hs

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Retained-passive raw-order change of variables with formal raw-order
determinant density, with the zero-tail and positive-tail cases packaged over
an arbitrary number of edges. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  cases M with
  | zero =>
      simpa using
        map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_zeroTail
          (ρ := ρ) (κ' := κ') m hs
  | succ M =>
      simpa [Nat.succ_eq_add_one] using
        map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_posTail
          (M := M) (ρ := ρ) (κ' := κ') m hs

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Retained-passive raw-order change of variables with the solved-`A1`
product determinant density, with the zero-tail and positive-tail cases
packaged over an arbitrary number of edges. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  cases M with
  | zero =>
      simpa using
        map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_zeroTail
          (ρ := ρ) (κ' := κ') m hs
  | succ M =>
      simpa [Nat.succ_eq_add_one] using
        map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_posTail
          (M := M) (ρ := ρ) (κ' := κ') m hs

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Localized retained-passive raw-order change of variables with the solved
`A1` product determinant density on any null-measurable patch inside the
determinant chart. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_image_of_subset_detChart
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    {Ω : Set (TopologyTuple ρ κ' ℝ)}
    (hΩ : NullMeasurableSet Ω m)
    (hΩdet :
      Ω ⊆ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict Ω).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') '' Ω) := by
  let Phi : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Jprod : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z ↦
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') z)
  let Jactual : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z ↦
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (M := M) (ρ := ρ) (κ' := κ') z)
  have hfderiv :
      ∀ z ∈ Ω,
        HasFDerivWithinAt Phi
          (fderiv ℝ Phi z) Ω z := by
    intro z hz
    exact
      (differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') z (hΩdet hz)).hasFDerivAt.hasFDerivWithinAt
  have hinj :
      Set.InjOn Phi Ω :=
    (injOn_topologyTupleEdgeRawOrder_detChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')).mono hΩdet
  have hcov_actual :
      Measure.map Phi ((m.restrict Ω).withDensity Jactual) =
        m.restrict (Phi '' Ω) := by
    simpa [Phi, Jactual, topologyTupleEdgeRawOrderFDerivAbsDet] using
      MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
        (μ := m) (s := Ω) (f := Phi) (f' := fun z ↦ fderiv ℝ Phi z)
        hΩ hfderiv hinj
  have hJ :
      Jprod =ᵐ[m.restrict Ω] Jactual := by
    filter_upwards [ae_restrict_mem₀ hΩ] with z hz
    simp [Jprod, Jactual,
      retainedPassiveFormalRawOrderJacobianProductAbsDetAt_eq_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
        (M := M) (ρ := ρ) (κ' := κ') (hΩdet hz)]
  calc
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict Ω).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
        Measure.map Phi ((m.restrict Ω).withDensity Jprod) := by
          rfl
    _ = Measure.map Phi ((m.restrict Ω).withDensity Jactual) := by
          rw [withDensity_congr_ae hJ]
    _ = m.restrict (Phi '' Ω) := hcov_actual
    _ =
        m.restrict
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') '' Ω) := by
          rfl

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Localized solved-`A1` product-determinant retained-passive raw-order change
of variables composed with an arbitrary a.e.-measurable target map. -/
theorem map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_image_of_subset_detChart
    {M : ℕ} {ρ β : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace β]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    {Ω : Set (TopologyTuple ρ κ' ℝ)}
    (ψ : TopologyTuple ρ κ' ℝ → β)
    (hΩ : NullMeasurableSet Ω m)
    (hΩdet :
      Ω ⊆ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (hψ :
      AEMeasurable ψ
        (m.restrict
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') '' Ω))) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          ψ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict Ω).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      Measure.map ψ
        (m.restrict
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') '' Ω)) := by
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let J : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z ↦
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') z)
  let μ : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict Ω).withDensity J
  have hΦ_contOn : ContinuousOn Φ Ω := by
    intro z hz
    exact
      (differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') z (hΩdet hz)).continuousAt.continuousWithinAt
  have hΦ_restrict : AEMeasurable Φ (m.restrict Ω) :=
    ContinuousOn.aemeasurable₀ hΦ_contOn hΩ
  have hΦ_μ : AEMeasurable Φ μ := by
    simpa [μ] using hΦ_restrict.mono_ac (withDensity_absolutelyContinuous _ _)
  have hcov :
      Measure.map Φ μ =
        m.restrict
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') '' Ω) := by
    simpa [Φ, J, μ] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_image_of_subset_detChart
        (M := M) (ρ := ρ) (κ' := κ') m hΩ hΩdet
  have hψ_map : AEMeasurable ψ (Measure.map Φ μ) := by
    rw [hcov]
    exact hψ
  calc
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ => ψ (Φ z)) μ =
        Measure.map ψ (Measure.map Φ μ) := by
          simpa [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable
              (μ := μ) (g := ψ) (f := Φ) hψ_map hΦ_μ).symm
    _ =
        Measure.map ψ
          (m.restrict
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') '' Ω)) := by
          rw [hcov]

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Patch-parametric solved-`A1` product-determinant retained-passive
raw-order change of variables.

If `P` is a raw-order source-recursive patch, the determinant-side patch
`detChart ∩ rawOrder ⁻¹' P` pushes exactly to Haar restricted to `P`. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_patch_of_subset_rawSource
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    {P : Set (TopologyTuple ρ κ' ℝ)}
    (hΩ :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ∩
          topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') ⁻¹' P) m)
    (hP :
      P ⊆
        topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict
            (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ∩
              topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') ⁻¹' P)).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      m.restrict P := by
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Ω : Set (TopologyTuple ρ κ' ℝ) := S ∩ Φ ⁻¹' P
  have hΩdet : Ω ⊆ S := by
    intro z hz
    exact hz.1
  have himage : Φ '' Ω = P := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.2
    · intro hy
      let z : TopologyTuple ρ κ' ℝ :=
        topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y
      have hzS : z ∈ S := by
        simpa [z, S, T] using
          topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ') (z := y) (hP hy)
      have hΦz : Φ z = y := by
        simpa [z, Φ, T] using
          topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := ρ) (κ' := κ') (z := y) (hP hy)
      refine ⟨z, ?_, hΦz⟩
      exact ⟨hzS, by simpa [hΦz] using hy⟩
  have hcov :
      Measure.map Φ
          ((m.restrict Ω).withDensity
            (fun z : TopologyTuple ρ κ' ℝ =>
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := M) (ρ := ρ) (κ' := κ') z))) =
        m.restrict (Φ '' Ω) := by
    simpa [Φ, S, Ω] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_image_of_subset_detChart
        (M := M) (ρ := ρ) (κ' := κ') m hΩ hΩdet
  simpa [Φ, S, Ω, himage] using hcov

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- Patch-parametric retained-passive raw-order COV composed with an arbitrary
a.e.-measurable post-map on the raw-order source patch. -/
theorem map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_patch_of_subset_rawSource
    {M : ℕ} {ρ β : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace β]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    {P : Set (TopologyTuple ρ κ' ℝ)}
    (ψ : TopologyTuple ρ κ' ℝ → β)
    (hΩ :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ∩
          topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') ⁻¹' P) m)
    (hP :
      P ⊆
        topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ'))
    (hψ : AEMeasurable ψ (m.restrict P)) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          ψ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict
            (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ∩
              topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') ⁻¹' P)).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      Measure.map ψ (m.restrict P) := by
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let Ω : Set (TopologyTuple ρ κ' ℝ) := S ∩ Φ ⁻¹' P
  have hΩdet : Ω ⊆ S := by
    intro z hz
    exact hz.1
  have himage : Φ '' Ω = P := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.2
    · intro hy
      let z : TopologyTuple ρ κ' ℝ :=
        topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y
      have hzS : z ∈ S := by
        simpa [z, S] using
          topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ') (z := y) (hP hy)
      have hΦz : Φ z = y := by
        simpa [z, Φ] using
          topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := ρ) (κ' := κ') (z := y) (hP hy)
      refine ⟨z, ?_, hΦz⟩
      exact ⟨hzS, by simpa [hΦz] using hy⟩
  have hψ_image : AEMeasurable ψ (m.restrict (Φ '' Ω)) := by
    simpa [himage] using hψ
  have hcov :
      Measure.map
          (fun z : TopologyTuple ρ κ' ℝ => ψ (Φ z))
          ((m.restrict Ω).withDensity
            (fun z : TopologyTuple ρ κ' ℝ =>
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := M) (ρ := ρ) (κ' := κ') z))) =
        Measure.map ψ (m.restrict (Φ '' Ω)) := by
    simpa [Φ, S, Ω] using
      map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_image_of_subset_detChart
        (M := M) (ρ := ρ) (κ' := κ') m (Ω := Ω) ψ hΩ hΩdet hψ_image
  simpa [Φ, S, Ω, himage] using hcov

private theorem map_comp_topologyTupleEdgeRawOrder_withDensity_eq_map_restrict_rawSourceChart_of_cov
    {M : ℕ} {ρ β : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace β]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (ψ : TopologyTuple ρ κ' ℝ → β)
    (J : TopologyTuple ρ κ' ℝ → ℝ≥0∞)
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hcov :
      Measure.map
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
          ((m.restrict
            (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity J) =
        m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))
    (hψ :
      AEMeasurable ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          ψ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity J) =
      Measure.map ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
  classical
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let μ : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict S).withDensity J
  have hΦ_contOn : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun z :
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_restrict : AEMeasurable Φ (m.restrict S) :=
    ContinuousOn.aemeasurable₀ hΦ_contOn (by simpa [S] using hs)
  have hΦ_μ : AEMeasurable Φ μ := by
    simpa [μ] using hΦ_restrict.mono_ac (withDensity_absolutelyContinuous _ _)
  have hcov' :
      Measure.map Φ μ = m.restrict T := by
    simpa [S, T, Φ, μ] using hcov
  have hψ_map : AEMeasurable ψ (Measure.map Φ μ) := by
    rw [hcov']
    simpa [T] using hψ
  calc
    Measure.map (fun z : TopologyTuple ρ κ' ℝ => ψ (Φ z)) μ =
        Measure.map ψ (Measure.map Φ μ) := by
          simpa [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable
              (μ := μ) (g := ψ) (f := Φ) hψ_map hΦ_μ).symm
    _ =
        Measure.map ψ (m.restrict T) := by
          rw [hcov']

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The formal-determinant retained-passive raw-order change of variables
composed with an arbitrary a.e.-measurable target map. -/
theorem map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_map_restrict_rawSourceChart
    {M : ℕ} {ρ β : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace β]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (ψ : TopologyTuple ρ κ' ℝ → β)
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hψ :
      AEMeasurable ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          ψ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      Measure.map ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
  let J : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') z)
  have hcov :
      Measure.map
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
          ((m.restrict
            (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity J) =
        m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')) := by
    simpa [J] using
      map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart
        (M := M) (ρ := ρ) (κ' := κ') m hs
  simpa [J] using
    map_comp_topologyTupleEdgeRawOrder_withDensity_eq_map_restrict_rawSourceChart_of_cov
      (M := M) (ρ := ρ) (κ' := κ') (β := β)
      m ψ J hs hcov hψ

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The solved-`A1` product-determinant retained-passive raw-order change of
variables composed with an arbitrary a.e.-measurable target map. -/
theorem map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_rawSourceChart
    {M : ℕ} {ρ β : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace β]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (ψ : TopologyTuple ρ κ' ℝ → β)
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hψ :
      AEMeasurable ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          ψ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      Measure.map ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
  let J : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') z)
  have hcov :
      Measure.map
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
          ((m.restrict
            (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity J) =
        m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')) := by
    simpa [J] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
        (M := M) (ρ := ρ) (κ' := κ') m hs
  simpa [J] using
    map_comp_topologyTupleEdgeRawOrder_withDensity_eq_map_restrict_rawSourceChart_of_cov
      (M := M) (ρ := ρ) (κ' := κ') (β := β)
      m ψ J hs hcov hψ

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
