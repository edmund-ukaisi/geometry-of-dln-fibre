import DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing

/-!
# Case 1 finite exponent-coordinate bridge

This file connects the finite selected-entry Case 1 local exponent
calculation to a supplied coordinate of finite normal-crossing exponent data.
It is deliberately only finite exponent bookkeeping: it does not construct
normal-crossing charts, prove global active-ratio lower bounds, prove chart
counts, or invoke the normal-crossing-to-RLCT extraction theorem.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Generic finite exponent-coordinate bridge saying that a coordinate in
finite normal-crossing exponent data has the Case 1 selected-entry exponents.

Both the selected-old chart and Aoyagi's displayed row-strip chart have loss
exponent `1` and formal Jacobian/prior exponent
`J1 * (n (S + 1) - J)`.  The structure records only those exponent-array
equalities for a supplied coordinate. -/
structure Case1SelectedEntryExponentCoordinateBridge
    (n : ℕ → ℕ) (S J J1 : ℕ)
    (D : AoyagiNormalCrossingExponentData)
    (p : Fin D.numCharts × Fin D.numCoords) : Prop where
  lossExp_eq_one : D.lossExp p.1 p.2 = 1
  jacobianPriorExp_eq_nonpivotCount :
    D.jacobianPriorExp p.1 p.2 = J1 * (n (S + 1) - J)

namespace Case1SelectedEntryExponentCoordinateBridge

/-- Build the generic Case 1 exponent-coordinate bridge when the matching
exponent equalities are stated on a chart certificate rather than on its
projected finite exponent data.

This is only a projection adapter.  It does not construct the chart
certificate, the coordinate, any chart coverage, or any analytic extraction
input. -/
theorem of_chartCertificate_coord_exponents
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hloss : Cnc.lossExp p.1 p.2 = 1)
    (hjac : Cnc.jacobianPriorExp p.1 p.2 = J1 * (n (S + 1) - J)) :
    Case1SelectedEntryExponentCoordinateBridge n S J J1
      Cnc.exponentData p where
  lossExp_eq_one := by
    simpa using hloss
  jacobianPriorExp_eq_nonpivotCount := by
    simpa using hjac

/-- A supplied finite exponent coordinate matching a Case 1 selected-entry
local step is active and has finite ratio
`(1 + J1 * (n(S+1)-J)) / 2`.

This is not a statement about the global minimum of `D`: that still requires
lower bounds over all active coordinates. -/
theorem activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryExponentCoordinateBridge n S J J1 D p) :
    p ∈ D.activePairs ∧
      D.ratioAt p = ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  refine ⟨D.mem_activePairs_of_lossExp_eq_one B.lossExp_eq_one, ?_⟩
  refine D.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq
    B.lossExp_eq_one ?_
  calc
    D.jacobianPriorExp p.1 p.2 + 1 =
        J1 * (n (S + 1) - J) + 1 := by
          rw [B.jacobianPriorExp_eq_nonpivotCount]
    _ = 1 + J1 * (n (S + 1) - J) := by
          omega

/-- Active-pair projection from the generic Case 1 exponent-coordinate
bridge. -/
theorem activePair
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryExponentCoordinateBridge n S J J1 D p) :
    p ∈ D.activePairs :=
  (B.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two).1

/-- Ratio projection from the generic Case 1 exponent-coordinate bridge. -/
theorem ratioAt_eq_nonpivotCount_add_one_div_two
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryExponentCoordinateBridge n S J J1 D p) :
    D.ratioAt p = ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
  (B.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two).2

/-- If the Case 1 local ratio lower-bounds every active coordinate, then it
is the finite exponent minimum of the supplied finite exponent data.

This does not prove the lower bound, construct exponent data, or prove any
chart/analytic statement. -/
theorem exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryExponentCoordinateBridge n S J J1 D p)
    (hle : ∀ p' ∈ D.activePairs,
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 ≤ D.ratioAt p') :
    D.exponentMinimum =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
  D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
    B.activePair B.ratioAt_eq_nonpivotCount_add_one_div_two hle

end Case1SelectedEntryExponentCoordinateBridge

/-- A0-facing wrapper around the generic Case 1 selected-entry
exponent-coordinate bridge.

Use this name only when the supplied finite exponent data is meant to be the
later A0 data for the full normal-crossing problem.  Local finite
microcertificates should use `Case1SelectedEntryExponentCoordinateBridge`
directly. -/
structure Case1SelectedEntryA0ExponentCoordinateBridge
    (n : ℕ → ℕ) (S J J1 : ℕ)
    (D : AoyagiNormalCrossingExponentData)
    (p : Fin D.numCharts × Fin D.numCoords) : Prop where
  toExponentCoordinateBridge :
    Case1SelectedEntryExponentCoordinateBridge n S J J1 D p

namespace Case1SelectedEntryA0ExponentCoordinateBridge

/-- Loss-exponent projection from the A0-facing wrapper. -/
theorem lossExp_eq_one
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p) :
    D.lossExp p.1 p.2 = 1 :=
  B.toExponentCoordinateBridge.lossExp_eq_one

/-- Formal-Jacobian/prior exponent projection from the A0-facing wrapper. -/
theorem jacobianPriorExp_eq_nonpivotCount
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p) :
    D.jacobianPriorExp p.1 p.2 = J1 * (n (S + 1) - J) :=
  B.toExponentCoordinateBridge.jacobianPriorExp_eq_nonpivotCount

/-- Build the supplied Case 1/A0 exponent-coordinate bridge when the matching
exponent equalities are stated on a chart certificate rather than on its
projected finite exponent data.

This is only a projection adapter.  It does not construct the chart
certificate, the coordinate, any chart coverage, or any analytic extraction
input. -/
theorem of_chartCertificate_coord_exponents
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hloss : Cnc.lossExp p.1 p.2 = 1)
    (hjac : Cnc.jacobianPriorExp p.1 p.2 = J1 * (n (S + 1) - J)) :
    Case1SelectedEntryA0ExponentCoordinateBridge n S J J1
      Cnc.exponentData p where
  toExponentCoordinateBridge :=
    Case1SelectedEntryExponentCoordinateBridge.of_chartCertificate_coord_exponents
      hloss hjac

/-- Active pair and ratio projection from the A0-facing wrapper. -/
theorem activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p) :
    p ∈ D.activePairs ∧
      D.ratioAt p = ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
  B.toExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two

/-- Active-pair projection from the A0-facing wrapper. -/
theorem activePair
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p) :
    p ∈ D.activePairs :=
  B.toExponentCoordinateBridge.activePair

/-- Ratio projection from the A0-facing wrapper. -/
theorem ratioAt_eq_nonpivotCount_add_one_div_two
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p) :
    D.ratioAt p = ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
  B.toExponentCoordinateBridge.ratioAt_eq_nonpivotCount_add_one_div_two

/-- If the Case 1 local ratio lower-bounds every active coordinate, then it
is the finite exponent minimum of the supplied A0 exponent data.

This does not prove the lower bound, construct the A0 exponent data, or prove
any chart/analytic statement. -/
theorem exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p)
    (hle : ∀ p' ∈ D.activePairs,
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 ≤ D.ratioAt p') :
    D.exponentMinimum =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
  B.toExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le hle

end Case1SelectedEntryA0ExponentCoordinateBridge

/-- Source-moving A0-facing wrapper for the selected-old Case 1 `Unit` chart
boundary.

The carried `Case1SelectedOldUnitSuppliedChartFamilyBoundary` records that the
finite selected-entry coordinate is intended to come from Aoyagi's Case 1(1)
selected-old boundary.  The exponent calculation still only uses the supplied
coordinate exponent equalities; this structure does not construct the A0
coordinate or any analytic chart data. -/
structure Case1SelectedOldUnitA0ExponentCoordinateBridge
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular)
    (D : AoyagiNormalCrossingExponentData)
    (p : Fin D.numCharts × Fin D.numCoords) : Prop where
  toA0ExponentCoordinateBridge :
    Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p

namespace Case1SelectedOldUnitA0ExponentCoordinateBridge

/-- Loss-exponent projection from the selected-old source-moving wrapper. -/
theorem lossExp_eq_one
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p) :
    D.lossExp p.1 p.2 = 1 :=
  B.toA0ExponentCoordinateBridge.lossExp_eq_one

/-- Formal-Jacobian/prior exponent projection from the selected-old
source-moving wrapper. -/
theorem jacobianPriorExp_eq_nonpivotCount
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p) :
    D.jacobianPriorExp p.1 p.2 = J1 * (n (S + 1) - J) :=
  B.toA0ExponentCoordinateBridge.jacobianPriorExp_eq_nonpivotCount

/-- Build the selected-old source-moving bridge from supplied exponent
equalities on finite exponent data. -/
theorem of_coord_exponents
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (hloss : D.lossExp p.1 p.2 = 1)
    (hjac : D.jacobianPriorExp p.1 p.2 = J1 * (n (S + 1) - J)) :
    Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p where
  toA0ExponentCoordinateBridge := {
    toExponentCoordinateBridge := {
      lossExp_eq_one := hloss
      jacobianPriorExp_eq_nonpivotCount := hjac } }

/-- Build the selected-old source-moving bridge when the matching exponent
equalities are stated on a chart certificate rather than on its projected
finite exponent data.

This is only a projection adapter.  It does not construct the chart
certificate, the coordinate, any chart coverage, or any analytic extraction
input. -/
theorem of_chartCertificate_coord_exponents
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {Param A : Type*} [CommMonoid A]
    {Cnc : AoyagiNormalCrossingChartCertificate Param A}
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hloss : Cnc.lossExp p.1 p.2 = 1)
    (hjac : Cnc.jacobianPriorExp p.1 p.2 = J1 * (n (S + 1) - J)) :
    Case1SelectedOldUnitA0ExponentCoordinateBridge cert Cnc.exponentData p where
  toA0ExponentCoordinateBridge :=
    Case1SelectedEntryA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents
      hloss hjac

/-- Active pair and ratio projection from the selected-old source-moving
wrapper. -/
theorem activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p) :
    p ∈ D.activePairs ∧
      D.ratioAt p = ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
  B.toA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two

/-- Active-pair projection from the selected-old source-moving wrapper. -/
theorem activePair
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p) :
    p ∈ D.activePairs :=
  B.toA0ExponentCoordinateBridge.activePair

/-- Ratio projection from the selected-old source-moving wrapper. -/
theorem ratioAt_eq_nonpivotCount_add_one_div_two
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p) :
    D.ratioAt p = ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
  B.toA0ExponentCoordinateBridge.ratioAt_eq_nonpivotCount_add_one_div_two

/-- If the selected-old Case 1 local ratio lower-bounds every active
coordinate, then it is the finite exponent minimum of the supplied A0 exponent
data.

This does not prove the lower bound, construct the A0 exponent data, or prove
any chart/analytic statement. -/
theorem exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p)
    (hle : ∀ p' ∈ D.activePairs,
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 ≤ D.ratioAt p') :
    D.exponentMinimum =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
  B.toA0ExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le hle

end Case1SelectedOldUnitA0ExponentCoordinateBridge

namespace case1SelectedOldCenterSqFormalJacobianChartCertificate

/-- The Case 1 selected-old finite microcertificate supplies the generic
Case 1 exponent-coordinate bridge for its own one-coordinate exponent data.

This does not identify the microcertificate with the full A0 chart family for
the DLN loss, and it does not prove any global active-ratio lower bound. -/
theorem localExponentCoordinateBridge
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Case1SelectedEntryExponentCoordinateBridge n S J J1
      (case1SelectedOldCenterSqFormalJacobianChartCertificate
        (K := K) n S J J1).exponentData
      ((0 : Fin 1), (0 : Fin 1)) where
  lossExp_eq_one := rfl
  jacobianPriorExp_eq_nonpivotCount := by
    exact jacobianPriorExp_zero_zero (K := K) n S J J1

end case1SelectedOldCenterSqFormalJacobianChartCertificate

namespace case1DisplayedRowStripCenterSqFormalJacobianChartCertificate

/-- The displayed Case 1 row-strip finite microcertificate supplies the
generic Case 1 exponent-coordinate bridge for its own one-coordinate exponent
data.

This does not identify the microcertificate with the full A0 chart family for
the DLN loss, and it does not prove any global active-ratio lower bound. -/
theorem localExponentCoordinateBridge
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Case1SelectedEntryExponentCoordinateBridge n S J J1
      (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
        (K := K) n S hJ1 hcol).exponentData
      ((0 : Fin 1), (0 : Fin 1)) where
  lossExp_eq_one := rfl
  jacobianPriorExp_eq_nonpivotCount := by
    exact jacobianPriorExp_zero_zero (K := K) n S hJ1 hcol

end case1DisplayedRowStripCenterSqFormalJacobianChartCertificate

end Aoyagi
end DLN
end DLNFibre
