import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex

/-!
# `IsAddHaarMeasure` for `DeepestSplit` (the PIN1 #72 Haar-blocker fix, route (b))

`#72` (`rlctAtOn_boundedUnit_localHomeomorph`) needs `(volume).IsAddHaarMeasure` on the ambient
space. `DeepestSplit H r nGauge = (Fin nReg → ℝ) × ((Fin flatM → ℝ) × (Fin nGauge → ℝ))` is a NESTED
PRODUCT, and `volume` on a `Prod` (= `Measure.prod`) does NOT synthesize `IsAddHaarMeasure` in Mathlib
v4.29 (verified: even a 2-factor `(Fin a → ℝ) × (Fin b → ℝ)` fails `infer_instance`). The flat
`Fin N → ℝ` DOES synthesize it. So we TRANSPORT: `DeepestSplit` is a `ContinuousLinearEquiv` image of
the flat space, and `ContinuousLinearEquiv.isAddHaarMeasure_map` carries the flat Haar across. -/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- `DeepestSplit` carries `IsAddHaarMeasure` — transported from the flat `Fin (nReg+flatM+nGauge) → ℝ`
(which synthesizes it) through the product-reindex `ContinuousLinearEquiv`. -/
instance instIsAddHaarMeasure_DeepestSplit (H : Fin (L + 1) → ℕ) (r nGauge : ℕ) :
    (volume : Measure (DeepestSplit H r nGauge)).IsAddHaarMeasure := by
  -- The product-reindex `(Fin nReg → ℝ) × ((Fin flatM → ℝ) × (Fin nGauge → ℝ))` as a CLE-image of
  -- itself reversed: each factor `Fin _ → ℝ` IS a finite-dim ℝ-space with `volume.IsAddHaarMeasure`;
  -- the obstruction is purely the `Prod`. Transport via the CLE `prodAssoc`-free route: exhibit
  -- DeepestSplit as `map e volume` for a CLE `e` from a space that DOES synthesize Haar.
  set nReg := deepestNReg H r
  set nM := flatDim (deepestM H r)
  -- The CLE folding the flat sum-Pi `((Fin nReg ⊕ (Fin nM ⊕ Fin nGauge)) → ℝ)` to the nested
  -- product `DeepestSplit = (Fin nReg → ℝ) × ((Fin nM → ℝ) × (Fin nGauge → ℝ))`.
  let eInner : ((Fin nM ⊕ Fin nGauge) → ℝ) ≃L[ℝ] (Fin nM → ℝ) × (Fin nGauge → ℝ) :=
    ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin nM) (Fin nGauge) (fun _ => ℝ)
  let eOuter : ((Fin nReg ⊕ (Fin nM ⊕ Fin nGauge)) → ℝ)
      ≃L[ℝ] (Fin nReg → ℝ) × ((Fin nM ⊕ Fin nGauge) → ℝ) :=
    ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin nReg) (Fin nM ⊕ Fin nGauge) (fun _ => ℝ)
  let e : ((Fin nReg ⊕ (Fin nM ⊕ Fin nGauge)) → ℝ) ≃L[ℝ] DeepestSplit H r nGauge :=
    eOuter.trans
      (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin nReg → ℝ)) eInner)
  -- `e` is a coordinate reindex: measure-preserving, so `map e volume = volume`.
  have hmpOuter : MeasurePreserving (eOuter)
      (volume : Measure ((Fin nReg ⊕ (Fin nM ⊕ Fin nGauge)) → ℝ)) volume :=
    volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin nReg ⊕ (Fin nM ⊕ Fin nGauge) => ℝ)
  have hmpInner : MeasurePreserving (eInner)
      (volume : Measure ((Fin nM ⊕ Fin nGauge) → ℝ)) volume :=
    volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin nM ⊕ Fin nGauge => ℝ)
  have hmpProd : MeasurePreserving
      (Prod.map (id : (Fin nReg → ℝ) → (Fin nReg → ℝ)) (eInner))
      (volume : Measure ((Fin nReg → ℝ) × ((Fin nM ⊕ Fin nGauge) → ℝ))) volume := by
    rw [show (volume : Measure ((Fin nReg → ℝ) × ((Fin nM ⊕ Fin nGauge) → ℝ)))
          = (volume : Measure (Fin nReg → ℝ)).prod volume from Measure.volume_eq_prod _ _,
      show (volume : Measure ((Fin nReg → ℝ) × ((Fin nM → ℝ) × (Fin nGauge → ℝ))))
          = (volume : Measure (Fin nReg → ℝ)).prod volume from Measure.volume_eq_prod _ _]
    exact (MeasurePreserving.id (volume : Measure (Fin nReg → ℝ))).prod hmpInner
  have hmp_e : MeasurePreserving (e)
      (volume : Measure ((Fin nReg ⊕ (Fin nM ⊕ Fin nGauge)) → ℝ)) volume :=
    hmpProd.comp hmpOuter
  have hmap : (volume : Measure (DeepestSplit H r nGauge))
      = Measure.map e (volume : Measure ((Fin nReg ⊕ (Fin nM ⊕ Fin nGauge)) → ℝ)) :=
    hmp_e.map_eq.symm
  rw [hmap]
  infer_instance

end DLNFibre.DLN.RLCT
