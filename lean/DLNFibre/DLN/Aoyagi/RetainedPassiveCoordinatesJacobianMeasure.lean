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
open scoped ENNReal Matrix.Norms.Operator

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
