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

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
