import DLNFibre.DLN.RLCT.Validate.D1HChartWire
import DLNFibre.DLN.RLCT.Foundations.S1IFTProducer
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartResidual` — the #231 `hchart` assembly (sub-build 5)

The capstone of the D1 `hchart` slot: turn the banked germ/chart/inverse blocks into the EXACT
`hchart` shape the §SEL engine consumer (`deepest_le_of_optimal_of_iftResidual`) demands:

    rlctAt H (dlnLoss H B) v
      = rlctAtOn (fun p : (Fin nReg → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) (0, t0),

with `Y = Fin (flatDim H − nReg) → ℝ`, `q` a GLOBAL `C¹` residual, and `t0` the reindex of the flat
origin. STATUS: SCAFFOLD — sub-builds being filled one at a time.
-/

open Matrix Module MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {H : Fin (2 + 1) → ℕ} {m : ℕ} {ec : Fin m → Fin (flatDim H)}

/-! ## Sub-build 1 — the measure-preserving split homeomorph `ℝ^N ≃ₜ ℝ^m × ℝ^(N−m)` -/

/-- The selected-membership predicate on flat coordinates: `c` is one of the `ec`-columns. -/
def selPred (ec : Fin m → Fin (flatDim H)) : Fin (flatDim H) → Prop := fun c => ∃ k, ec k = c

/-- `ec` injective reindexes the SELECTED subtype `{c // ∃ k, ec k = c}` onto `Fin m`. -/
noncomputable def selEquiv (hec : Function.Injective ec) :
    Fin m ≃ {c : Fin (flatDim H) // selPred ec c} where
  toFun k := ⟨ec k, ⟨k, rfl⟩⟩
  invFun c := c.2.choose
  left_inv k := hec (Exists.choose_spec (⟨k, rfl⟩ : selPred ec (ec k)))
  right_inv c := Subtype.ext c.2.choose_spec

instance instDecidableSelPred (ec : Fin m → Fin (flatDim H)) : DecidablePred (selPred ec) :=
  fun c => Fintype.decidableExistsFintype

/-- The COMPLEMENT subtype `{c // ¬ selPred ec c}` has cardinality `flatDim H − m`. -/
theorem card_complSub (hec : Function.Injective ec) :
    Fintype.card {c : Fin (flatDim H) // ¬ selPred ec c} = flatDim H - m := by
  classical
  rw [Fintype.card_subtype_compl]
  have hsel : Fintype.card {c : Fin (flatDim H) // selPred ec c} = m := by
    rw [← Fintype.card_congr (selEquiv hec), Fintype.card_fin]
  rw [hsel, Fintype.card_fin]

/-- Reindex the COMPLEMENT subtype to `Fin (flatDim H − m)` (card bridge). -/
noncomputable def complEquiv (hec : Function.Injective ec) :
    Fin (flatDim H - m) ≃ {c : Fin (flatDim H) // ¬ selPred ec c} :=
  (finCongr (card_complSub hec).symm).trans (Fintype.equivFin _).symm

/-- **The split homeomorph** `ℝ^N ≃ₜ ℝ^m × ℝ^(N−m)`: separate the selected `ec`-columns from the
complement, then reindex each subtype factor to a `Fin`. The selected slot `k` reads coordinate
`ec k` (`splitHomeo_fst_apply`). -/
noncomputable def splitHomeo (hec : Function.Injective ec) :
    (Fin (flatDim H) → ℝ) ≃ₜ ((Fin m → ℝ) × (Fin (flatDim H - m) → ℝ)) :=
  (Homeomorph.piEquivPiSubtypeProd (selPred ec) (fun _ => ℝ)).trans
    ((Homeomorph.piCongrLeft (Y := fun _ : {c // selPred ec c} => ℝ) (selEquiv hec)).symm.prodCongr
      (Homeomorph.piCongrLeft (Y := fun _ : {c // ¬ selPred ec c} => ℝ) (complEquiv hec)).symm)

/-- The selected slot `k` of `splitHomeo` reads the `ec k` flat coordinate. -/
theorem splitHomeo_fst_apply (hec : Function.Injective ec) (w : Fin (flatDim H) → ℝ) (k : Fin m) :
    (splitHomeo hec w).1 k = w (ec k) := by
  simp only [splitHomeo, Homeomorph.trans_apply, Homeomorph.coe_prodCongr, Prod.map_apply,
    Homeomorph.piCongrLeft_symm_apply]
  rfl

/-- `splitHomeo` is measure-preserving (volume on the flat space ↔ product volume). -/
theorem splitHomeo_mp (hec : Function.Injective ec) :
    MeasurePreserving (splitHomeo hec)
      (volume : Measure (Fin (flatDim H) → ℝ)) volume := by
  have hA : MeasurePreserving
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {c // selPred ec c} => ℝ) (selEquiv hec)).symm
      volume volume :=
    MeasurePreserving.symm _
      (volume_measurePreserving_piCongrLeft (fun _ : {c // selPred ec c} => ℝ) (selEquiv hec))
  have hB : MeasurePreserving
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {c // ¬ selPred ec c} => ℝ) (complEquiv hec)).symm
      volume volume :=
    MeasurePreserving.symm _
      (volume_measurePreserving_piCongrLeft (fun _ : {c // ¬ selPred ec c} => ℝ) (complEquiv hec))
  have hpiv := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin (flatDim H) => ℝ) (selPred ec)
  have hprod := hA.prod hB
  exact hprod.comp hpiv

/-- `splitHomeo` is a measurable embedding (it is a homeomorphism). -/
theorem splitHomeo_emb (hec : Function.Injective ec) :
    MeasurableEmbedding (splitHomeo hec) :=
  (splitHomeo hec).measurableEmbedding

end DLNFibre.DLN.RLCT
