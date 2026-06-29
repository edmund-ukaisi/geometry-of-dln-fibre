import DLNFibre.DLN.RLCT.Foundations.S1IFTChart
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import DLNFibre.DLN.RLCT.Foundations.LossContinuity
import Mathlib.MeasureTheory.Group.Measure

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartFlatten` — the flatten + translate bridge for the D1 `hchart`

The measure-preserving plumbing that moves the D1 loss off `Params H` onto the flat space
`Fin N → ℝ` with the basepoint translated to the origin — the prerequisite for instantiating the
banked abstract `hchart` (`rlctAtOn_eq_of_contDiff_chart`, `S1IFTChart`) with the concrete DLN
selected-minor chart.

Two MP steps, both `rlctAtOn_comp_homeomorph`:
  * **flatten** `paramsEquivFlat H : Params H ≃ᵐ (Fin (flatDim H) → ℝ)` (banked, MP):
    `rlctAt H (dlnLoss H B) v = rlctAtOn (dlnLoss H B ∘ flatSymm) (flat v)`;
  * **translate** `Homeomorph.addRight (flat v)` (Haar-invariant on `Fin N → ℝ`):
    `rlctAtOn (dlnLoss∘flatSymm) (flat v) = rlctAtOn (dlnLoss∘flatSymm ∘ (· + flat v)) 0`.

Composed: `rlctAt H (dlnLoss H B) v = rlctAtOn (lossFlatShift H B v) 0`, basepoint at the flat
origin (where the IFT chart `Φ` fixes `0`). STATUS: built sorry-free, axiom-clean.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The D1 loss in FLAT, ORIGIN-CENTRED coordinates: `dlnLoss H B` precomposed with the flat-inverse
and the translation by the flat image of `v`. Its local RLCT at the flat origin `0` equals
`rlctAt H (dlnLoss H B) v` (`rlctAt_eq_rlctAtOn_lossFlatShift`). -/
noncomputable def lossFlatShift (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H) :
    (Fin (flatDim H) → ℝ) → ℝ :=
  fun w => dlnLoss H B ((paramsEquivFlat H).symm (w + (paramsEquivFlat H) v))

/-- **The flatten + translate bridge.** The local RLCT of the D1 loss `dlnLoss H B` at the optimal
point `v` equals that of the flat, origin-centred `lossFlatShift H B v` at `0`:

    rlctAt H (dlnLoss H B) v = rlctAtOn (lossFlatShift H B v) 0.

Two measure-preserving changes of variable (`rlctAtOn_comp_homeomorph`): the flatten
`paramsEquivFlat H` (banked MP) then the translation `(· + flat v)` (Haar-invariant). The basepoint
lands at the flat origin, where the IFT chart fixes `0`. -/
theorem rlctAt_eq_rlctAtOn_lossFlatShift (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H) :
    rlctAt H (dlnLoss H B) v = rlctAtOn (lossFlatShift H B v) (0 : Fin (flatDim H) → ℝ) := by
  -- Step 1: flatten via `paramsEquivFlat H` (MP homeomorph), basepoint `v ↦ flat v`.
  set e : Params H ≃ₜ (Fin (flatDim H) → ℝ) :=
    ⟨(paramsEquivFlat H).toEquiv, continuous_paramsEquivFlat H, continuous_paramsEquivFlat_symm H⟩
    with he
  have hmp : MeasurePreserving e (volume : Measure (Params H)) volume :=
    measurePreserving_paramsEquivFlat H
  have hemb : MeasurableEmbedding e := (paramsEquivFlat H).measurableEmbedding
  have hstep1 := rlctAtOn_comp_homeomorph e hmp hemb
    (fun w : Fin (flatDim H) → ℝ => dlnLoss H B ((paramsEquivFlat H).symm w)) v
  have hcomp1 : (fun A : Params H => dlnLoss H B ((paramsEquivFlat H).symm (e A)))
      = fun A : Params H => dlnLoss H B A := by
    funext A; congr 1; exact (paramsEquivFlat H).symm_apply_apply A
  rw [hcomp1] at hstep1
  have he_v : e v = (paramsEquivFlat H) v := rfl
  rw [he_v] at hstep1
  -- now `hstep1 : rlctAtOn (dlnLoss H B) v = rlctAtOn (loss∘flatSymm) (flat v)` … but actually
  -- `rlctAtOn` on `Params` = `rlctAt`. Convert.
  rw [← rlctAtOn_eq_rlctAt H (dlnLoss H B) v, hstep1]
  -- Step 2: translate by `flat v` (MP, Haar), basepoint `0 ↦ flat v` via `addRight`.
  set τ : (Fin (flatDim H) → ℝ) ≃ₜ (Fin (flatDim H) → ℝ) :=
    Homeomorph.addRight ((paramsEquivFlat H) v) with hτ
  have hτmp : MeasurePreserving τ (volume : Measure (Fin (flatDim H) → ℝ)) volume := by
    rw [hτ]; exact measurePreserving_add_right volume ((paramsEquivFlat H) v)
  have hτemb : MeasurableEmbedding τ := τ.measurableEmbedding
  have hstep2 := rlctAtOn_comp_homeomorph τ hτmp hτemb
    (fun w : Fin (flatDim H) → ℝ => dlnLoss H B ((paramsEquivFlat H).symm w))
    (0 : Fin (flatDim H) → ℝ)
  have hτ0 : τ (0 : Fin (flatDim H) → ℝ) = (paramsEquivFlat H) v := by
    rw [hτ]; simp [Homeomorph.addRight]
  rw [hτ0] at hstep2
  rw [← hstep2]
  rfl

end DLNFibre.DLN.RLCT
