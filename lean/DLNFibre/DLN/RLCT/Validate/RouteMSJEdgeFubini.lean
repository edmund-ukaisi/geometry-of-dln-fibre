import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeWiring
import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeCShift

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeFubini` — the b=1 edge Fubini transport (connective tissue, measure side)

Thread `genm-tideD` (edge dispatch arm, b=1 a<u brick). The **measure-side transport** turning the edge
cell's `coupledBoxIntegrand` inner `∫_x ∫_Γ` into the form the C-shift atoms (`edge_leaf_gamma_bound`,
`RouteMSJEdgeCShift`) close.

* `shearBox_lintegral_eq` — the schur-shear CoV `∫_Γ in shearBox = ∫_D in genBox` (translation
  `D = Γ + schurShift x`, measure-preserving), moving to the FRONT-DECOUPLED sheared loss
  (`freedSchurLoss_shear_eq`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-- **The schur-shear change-of-variables.** For fixed front `x` and deep factor `Q`, the inner
`Γ`-integral over the shear-image box `{Γ | Γ + schurShift x ∈ genBox}` equals the `D`-integral over the
centered `genBox` of the SHEARED loss `freedSchurLoss x (D − schurShift x) Q`. The translation
`D = Γ + schurShift x` is measure-preserving and maps the shear-image box onto `genBox`
(`measurePreserving_add_right` + `setLIntegral_comp_preimage_emb`, the `chartInner_schurShearFree_eq`
template in reverse). Composing with `freedSchurLoss_shear_eq` puts the corank term in the
front-decoupled `frobSq(C·Q_inl + D·Q_inr)` form. -/
theorem shearBox_lintegral_eq {u a b n : ℕ} (x : SJOuter u a b)
    (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ) (c' T : ℝ) :
    (∫⁻ Γ in {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T},
        ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')))
      = ∫⁻ D in genBox (Fin a) (Fin b) T,
          ENNReal.ofReal ((freedSchurLoss x (D - schurShift x) Q) ^ (-c')) := by
  have hshear := (measurePreserving_add_right (volume : Measure (Fin a → Fin b → ℝ))
      (schurShift x)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight (schurShift x))
    (fun D => ENNReal.ofReal ((freedSchurLoss x (D - schurShift x) Q) ^ (-c')))
    (genBox (Fin a) (Fin b) T)
  rw [← hshear]
  simp only [add_sub_cancel_right]
  rfl

end DLNFibre.DLN.RLCT
