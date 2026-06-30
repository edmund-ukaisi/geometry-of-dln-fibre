import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge

/-!
# Case 2 retained-passive passive-sector coordinates

This file packages the full passive-sector coordinate vector for the Case 2
selected-entry retained-passive chart.  It adds no measure transport theorem:
the results here only build the coordinate domain and prove determinant-chart
membership from the passive determinant-unit conditions.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

namespace Case2PassiveTheta

/-- The successor selected-entry residual center coordinates in the Case 2
continuing branch. -/
abbrev Center (n : ℕ → ℕ) (S J : ℕ) :=
  {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}

set_option linter.style.longLine false in
/-- The passive retained p.13 coordinates suppressed by the reduced
selected-entry section. -/
abbrev PassiveFields {ρ : Type*} {τ : Type} (n : ℕ → ℕ) (S J : ℕ) :=
  (Fin 1 → Matrix ρ ρ ℝ) ×
    ((∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ) ×
      ((∀ p : Fin 1,
        Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) ×
        (Matrix ρ ρ ℝ ×
          Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)))

end Case2PassiveTheta

set_option linter.style.longLine false in
/-- Full passive-sector coordinate vector for the Case 2 post-pivot
selected-entry retained-passive datum. -/
abbrev Case2PassiveTheta {ρ : Type*} {τ : Type} (n : ℕ → ℕ) (S J : ℕ) :=
  Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J ×
    (Case2PassiveTheta.Center n S J → ℝ)

namespace Case2PassiveTheta

set_option linter.style.longLine false in
/-- Constructor for the full passive-sector coordinate vector. -/
def mk {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext : Center n S J → ℝ) :
    Case2PassiveTheta (ρ := ρ) (τ := τ) n S J :=
  ((A1passive, (F2, (A3passive, (Ctop, F3)))), yNext)

/-- Passive `A1` blocks. -/
def A1passive {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :
    Fin 1 → Matrix ρ ρ ℝ :=
  theta.1.1

set_option linter.style.longLine false in
/-- Passive upper-right blocks. -/
def F2 {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :
    ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ :=
  theta.1.2.1

set_option linter.style.longLine false in
/-- Passive lower-left blocks. -/
def A3passive {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :
    ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ :=
  theta.1.2.2.1

/-- Endpoint top-left block. -/
def Ctop {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :
    Matrix ρ ρ ℝ :=
  theta.1.2.2.2.1

set_option linter.style.longLine false in
/-- Endpoint lower-left block. -/
def F3 {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :
    Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ :=
  theta.1.2.2.2.2

/-- Successor selected-entry residual center coordinates. -/
def yNext {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :
    Center n S J → ℝ :=
  theta.2

@[simp]
theorem A1passive_mk {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext : Center n S J → ℝ) :
    (mk (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      A1passive F2 A3passive Ctop F3 yNext).A1passive = A1passive := rfl

@[simp]
theorem F2_mk {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext : Center n S J → ℝ) :
    (mk (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      A1passive F2 A3passive Ctop F3 yNext).F2 = F2 := rfl

@[simp]
theorem A3passive_mk {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext : Center n S J → ℝ) :
    (mk (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      A1passive F2 A3passive Ctop F3 yNext).A3passive = A3passive := rfl

@[simp]
theorem Ctop_mk {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext : Center n S J → ℝ) :
    (mk (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      A1passive F2 A3passive Ctop F3 yNext).Ctop = Ctop := rfl

@[simp]
theorem F3_mk {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext : Center n S J → ℝ) :
    (mk (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      A1passive F2 A3passive Ctop F3 yNext).F3 = F3 := rfl

@[simp]
theorem yNext_mk {ρ : Type*} {τ : Type} {n : ℕ → ℕ} {S J : ℕ}
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext : Center n S J → ℝ) :
    (mk (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      A1passive F2 A3passive Ctop F3 yNext).yNext = yNext := rfl

end Case2PassiveTheta

set_option linter.style.longLine false in
/-- The successor selected pivot coordinate in the Case 2 continuing branch. -/
def case2PassiveThetaPivotNext (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1)) :
    Case2PassiveTheta.Center n S J :=
  ⟨(J + 2, J + 2),
    case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩

set_option linter.style.longLine false in
/-- The selected pivot coordinate is nonzero.  This is the punctured
selected-entry condition, separate from retained determinant-chart membership. -/
def case2PassiveThetaPivotNonzero
    {ρ : Type*} {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) : Prop :=
  theta.yNext (case2PassiveThetaPivotNext n hS hnext) ≠ 0

set_option linter.style.longLine false in
/-- Passive determinant-sector condition for the retained-passive chart. -/
def case2PassiveThetaDetSector
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) (S J : ℕ) :
    Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
  {theta | IsUnit theta.Ctop.det ∧ ∀ p : Fin 1, IsUnit ((theta.A1passive p).det)}

set_option linter.style.longLine false in
/-- Passive determinant sector together with the nonzero selected pivot. -/
def case2PassiveThetaPuncturedDetSector
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1)) :
    Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
  {theta | theta ∈ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J ∧
    case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext theta}

set_option linter.style.longLine false in
/-- Retained-passive data produced from a full passive-sector coordinate
vector before endpoint transport. -/
noncomputable def case2PassiveThetaRetainedData
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    RetainedPassiveNonredundantCoordinateData
      (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) :=
  case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    (ρ := ρ) n hS hcont hnext
    theta.A1passive theta.F2 theta.A3passive theta.Ctop theta.F3 theta.yNext eNext

set_option linter.style.longLine false in
/-- Endpoint-transported retained-passive data produced from a full
passive-sector coordinate vector. -/
noncomputable def case2PassiveThetaEndpointRetainedData
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' :=
  (case2PassiveThetaRetainedData (ρ := ρ) n hS hcont hnext theta eNext).endpointTransport e

set_option linter.style.longLine false in
/-- Product-topology tuple of retained-passive fields produced from a full
passive-sector coordinate vector before endpoint transport. -/
noncomputable def case2PassiveThetaTopologyTuple
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    TopologyTuple ρ (case2PostPivotTwoEdgeDomain n S J τ) ℝ :=
  topologyTuple
    (case2PassiveThetaRetainedData (ρ := ρ) n hS hcont hnext theta eNext)

set_option linter.style.longLine false in
/-- Product-topology tuple of retained-passive fields produced from a full
passive-sector coordinate vector after endpoint transport. -/
noncomputable def case2PassiveThetaEndpointTopologyTuple
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    TopologyTuple ρ κ' ℝ :=
  topologyTuple
    (case2PassiveThetaEndpointRetainedData
      (ρ := ρ) n hS hcont hnext theta eNext e)

set_option linter.style.longLine false in
/-- Image sector in topology-tuple coordinates for a full passive theta domain
before endpoint transport.  This names the target set for later sector-measure
statements; it is not a measure-transport theorem. -/
noncomputable def case2PassiveThetaSectorSet
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)) :
    Set (TopologyTuple ρ (case2PostPivotTwoEdgeDomain n S J τ) ℝ) :=
  (fun theta ↦
    case2PassiveThetaTopologyTuple
      (ρ := ρ) n hS hcont hnext theta eNext) '' Ω

set_option linter.style.longLine false in
/-- Image sector in endpoint-transported topology-tuple coordinates for a full
passive theta domain.  This is the named sector target needed before exact or
dominated passive-sector measure comparisons can be stated. -/
noncomputable def case2PassiveThetaEndpointSectorSet
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)) :
    Set (TopologyTuple ρ κ' ℝ) :=
  (fun theta ↦
    case2PassiveThetaEndpointTopologyTuple
      (ρ := ρ) n hS hcont hnext theta eNext e) '' Ω

set_option linter.style.longLine false in
/-- The full passive-sector coordinate map to retained-passive data is
continuous in the product topology. -/
theorem continuous_case2PassiveThetaRetainedData
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    Continuous
      (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaRetainedData
          (ρ := ρ) n hS hcont hnext theta eNext) := by
  let η :=
    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J
  have hA1passive_cont :
      Continuous (fun z : η ↦ z.1) :=
    continuous_fst
  have hF2_cont :
      Continuous (fun z : η ↦ z.2.1) :=
    continuous_fst.comp continuous_snd
  have hA3passive_cont :
      Continuous (fun z : η ↦ z.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hCtop_cont :
      Continuous (fun z : η ↦ z.2.2.2.1) :=
    continuous_fst.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hF3_cont :
      Continuous (fun z : η ↦ z.2.2.2.2) :=
    continuous_snd.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  simpa [case2PassiveThetaRetainedData, Case2PassiveTheta.A1passive,
    Case2PassiveTheta.F2, Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
    Case2PassiveTheta.F3, Case2PassiveTheta.yNext, η] using
    continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
      (ρ := ρ) n hS hcont hnext
      (fun z : η ↦ z.1) (fun z : η ↦ z.2.1) (fun z : η ↦ z.2.2.1)
      (fun z : η ↦ z.2.2.2.1) (fun z : η ↦ z.2.2.2.2) eNext
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont

set_option linter.style.longLine false in
/-- The full passive-sector coordinate map to endpoint-transported
retained-passive data is continuous in the product topology. -/
theorem continuous_case2PassiveThetaEndpointRetainedData
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    Continuous
      (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := ρ) n hS hcont hnext theta eNext e) := by
  change Continuous
    (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
      (case2PassiveThetaRetainedData
        (ρ := ρ) n hS hcont hnext theta eNext).endpointTransport e)
  exact
    (continuous_endpointTransport (K := ℝ) (ρ := ρ) e).comp
      (continuous_case2PassiveThetaRetainedData
        (ρ := ρ) n hS hcont hnext eNext)

set_option linter.style.longLine false in
/-- The full passive-sector coordinate map to retained-passive topology tuples
is continuous. -/
theorem continuous_case2PassiveThetaTopologyTuple
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    Continuous
      (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext) := by
  change Continuous
    (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
      topologyTuple
        (case2PassiveThetaRetainedData
          (ρ := ρ) n hS hcont hnext theta eNext))
  exact
    (continuous_topologyTuple
      (K := ℝ) (ρ := ρ) (κ' := case2PostPivotTwoEdgeDomain n S J τ)).comp
      (continuous_case2PassiveThetaRetainedData
        (ρ := ρ) n hS hcont hnext eNext)

set_option linter.style.longLine false in
/-- The full passive-sector coordinate map to endpoint-transported
retained-passive topology tuples is continuous. -/
theorem continuous_case2PassiveThetaEndpointTopologyTuple
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    Continuous
      (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e) := by
  change Continuous
    (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
      topologyTuple
        (case2PassiveThetaEndpointRetainedData
          (ρ := ρ) n hS hcont hnext theta eNext e))
  exact
    (continuous_topologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')).comp
      (continuous_case2PassiveThetaEndpointRetainedData
        (ρ := ρ) n hS hcont hnext eNext e)

set_option linter.style.longLine false in
/-- Full passive-sector coordinates in the determinant sector produce
retained-passive determinant-chart data before endpoint transport. -/
theorem case2PassiveThetaRetainedData_detChart
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hdet :
      theta ∈ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J) :
    (case2PassiveThetaRetainedData
      (ρ := ρ) n hS hcont hnext theta eNext).detChart := by
  exact
    case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_detChart
      (ρ := ρ) n hS hcont hnext
      theta.A1passive theta.F2 theta.A3passive theta.Ctop theta.F3
      theta.yNext eNext hdet.1 hdet.2

set_option linter.style.longLine false in
/-- Full passive-sector coordinates in the determinant sector produce
retained-passive determinant-chart data after endpoint transport. -/
theorem case2PassiveThetaEndpointRetainedData_detChart
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (hdet :
      theta ∈ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J) :
    (case2PassiveThetaEndpointRetainedData
      (ρ := ρ) n hS hcont hnext theta eNext e).detChart := by
  exact
    case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
      (ρ := ρ) n hS hcont hnext
      theta.A1passive theta.F2 theta.A3passive theta.Ctop theta.F3
      theta.yNext eNext e hdet.1 hdet.2

set_option linter.style.longLine false in
/-- The pre-transport passive theta tuple lies in the retained-passive
determinant-chart set under the passive determinant-sector condition. -/
theorem case2PassiveThetaTopologyTuple_mem_detChartSet
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hdet :
      theta ∈ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J) :
    case2PassiveThetaTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext ∈
      topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := case2PostPivotTwoEdgeDomain n S J τ) := by
  have hdata :
      (case2PassiveThetaRetainedData
        (ρ := ρ) n hS hcont hnext theta eNext).detChart :=
    case2PassiveThetaRetainedData_detChart
      (ρ := ρ) n hS hcont hnext theta eNext hdet
  simpa [case2PassiveThetaTopologyTuple] using
    (topologyTuple_mem_topologyTupleDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := case2PostPivotTwoEdgeDomain n S J τ)
      (case2PassiveThetaRetainedData
        (ρ := ρ) n hS hcont hnext theta eNext)).2 hdata

set_option linter.style.longLine false in
/-- The endpoint-transported passive theta tuple lies in the retained-passive
determinant-chart set under the passive determinant-sector condition. -/
theorem case2PassiveThetaEndpointTopologyTuple_mem_detChartSet
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (hdet :
      theta ∈ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J) :
    case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e ∈
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
  have hdata :
      (case2PassiveThetaEndpointRetainedData
        (ρ := ρ) n hS hcont hnext theta eNext e).detChart :=
    case2PassiveThetaEndpointRetainedData_detChart
      (ρ := ρ) n hS hcont hnext theta eNext e hdet
  simpa [case2PassiveThetaEndpointTopologyTuple] using
    (topologyTuple_mem_topologyTupleDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
      (case2PassiveThetaEndpointRetainedData
        (ρ := ρ) n hS hcont hnext theta eNext e)).2 hdata

end Aoyagi
end DLN
end DLNFibre
