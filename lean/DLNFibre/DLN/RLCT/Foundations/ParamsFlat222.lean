import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `DLNFibre.DLN.RLCT.Foundations.ParamsFlat222` — the explicit `(2,2,2)` flatten seam

The `(2,2,2)` resolution cover is built on the flat host `Fin 8 → ℝ` with the EXPLICIT coordinate
convention `a00=0, a01=1, a10=2, a11=3, b00=4, b01=5, b10=6, b11=7` (slots 0-3 = the `A` matrix
row-major, 4-7 = `B`). To connect `rlctAt (dlnLoss (2,2,2)) (deepest)` (on `Params`) to
`rlctAtOn myF222 0` (on `Fin 8 → ℝ`), we need a **measure-preserving** equivalence
`e222 : Params (2,2,2) ≃ᵐ (Fin 8 → ℝ)` realizing exactly that order.

This is `paramsEquivFlat`'s construction (two `piCurry` collapses of the nested `Pi`, then one
`arrowCongr'` reindex) but with the **explicit computable** bijection `fin8EquivFlatIdx222 : Fin 8 ≃
FlatIdx (2,2,2)` in place of the noncomputable `Fintype.equivFin` — so the slot↔entry identification
is pinned BY CONSTRUCTION (no `equivFin` enumeration, which is irreducibly noncomputable), and the
measure-preservation reuses `measurePreserving_piCurry` + `volume_preserving_arrowCongr'` verbatim.
The construction never forms a binary product, sidestepping the absent `MeasureSpace (α × β)`.
-/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

/-- The `(2,2,2)` width vector (`L = 2`, all widths `2`). -/
def H222 : Fin 3 → ℕ := fun _ => 2

/-- The explicit computable bijection `Fin 8 ≃ FlatIdx (2,2,2)`, row-major `k = j + 2·i + 4·s`
(`0 ↦ (s=0,i=0,j=0) = a00`, …, `7 ↦ (s=1,i=1,j=1) = b11`). All `Fin` bounds are the constant `2`, so
the dependent `Σ` strips to a product via `Equiv.sigmaEquivProd`; the `Fin`-product chain is
`finProdFinEquiv`. Computable — pins the slot↔entry identification with no `Fintype.equivFin`. -/
def fin8EquivFlatIdx222 : Fin 8 ≃ FlatIdx H222 :=
  (((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).prodCongr (Equiv.refl (Fin 2))).trans
      (finProdFinEquiv : Fin (2 * 2) × Fin 2 ≃ Fin ((2 * 2) * 2))).symm.trans
    ((Equiv.sigmaEquivProd (Σ _ : Fin 2, Fin 2) (Fin 2)).trans
      ((Equiv.sigmaEquivProd (Fin 2) (Fin 2)).prodCongr (Equiv.refl (Fin 2)))).symm

/-- **The `(2,2,2)` flatten.** `Params (2,2,2) ≃ᵐ (Fin 8 → ℝ)` in the explicit `a00=0..b11=7`
order: the two `piCurry` collapses of the nested `Pi` (as in `paramsEquivFlat`), then the
`arrowCongr'` reindex by `fin8EquivFlatIdx222.symm` (not the noncomputable `equivFin`). -/
noncomputable def e222 : Params H222 ≃ᵐ (Fin 8 → ℝ) :=
  (MeasurableEquiv.piCurry
      (fun (s : Fin 2) (_ : Fin (H222 s.castSucc)) => Fin (H222 s.succ) → ℝ)).symm.trans
    ((MeasurableEquiv.piCurry (fun (q : FlatRowIdx H222) (_ : Fin (H222 q.1.succ)) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' fin8EquivFlatIdx222.symm (MeasurableEquiv.refl ℝ)))

/-- **The seam (measure side).** `e222` is measure-preserving for the product Lebesgue measures —
reusing `measurePreserving_piCurry` (×2, `.symm`) + `volume_preserving_arrowCongr'` (which holds for
the explicit equiv exactly as for any equiv). So any RLCT/integrability fact on `Fin 8 → ℝ`
transports to `Params (2,2,2)` and back, identification pinned by `fin8EquivFlatIdx222`. -/
theorem measurePreserving_e222 :
    MeasurePreserving e222 (volume : Measure (Params H222)) (volume : Measure (Fin 8 → ℝ)) := by
  unfold e222
  have h1 := measurePreserving_piCurry
    (fun (s : Fin 2) (_ : Fin (H222 s.castSucc)) => Fin (H222 s.succ) → ℝ)
    (fun q _ => (volume : Measure (Fin (H222 q.succ) → ℝ)))
  have h2 := measurePreserving_piCurry
    (fun (q : FlatRowIdx H222) (_ : Fin (H222 q.1.succ)) => ℝ) (fun _ _ => (volume : Measure ℝ))
  have ha := volume_preserving_arrowCongr' fin8EquivFlatIdx222.symm (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id (volume : Measure ℝ))
  exact (h1.symm _).trans ((h2.symm _).trans ha)

/-! ## The coordinate identification (the seam's fidelity realization)

`e222.symm` recovers each matrix entry from its flat slot — DEFINITIONALLY (`rfl`), since the equiv
is a `piCurry`-collapse + reindex (the extraction mirrors `prod_paramsEquivFlat`'s `rfl`). Composing
with the explicit `fin8EquivFlatIdx222` slot table (`decide`, kernel) pins `a00=0, …, b11=7`. So the
coordinate identification is PROVEN and auditable, not asserted. -/

/-- **Coordinate extraction (`rfl`).** The `(s,i,j)` matrix entry of `e222.symm x` is the flat
coordinate `x` at the slot `fin8EquivFlatIdx222.symm ⟨⟨s,i⟩,j⟩`. -/
theorem e222_symm_coord (x : Fin 8 → ℝ) (s i j : Fin 2) :
    (e222.symm x) s i j = x (fin8EquivFlatIdx222.symm (⟨⟨s, i⟩, j⟩ : FlatIdx H222)) := rfl

/-- The `A`-block slots (`s = 0`): `a00=0, a01=1, a10=2, a11=3`. By `decide` (kernel). -/
theorem slot_a00 :
    fin8EquivFlatIdx222.symm (⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ⟨0, by decide⟩⟩ : FlatIdx H222)
      = 0 := by decide
theorem slot_a01 :
    fin8EquivFlatIdx222.symm (⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ⟨1, by decide⟩⟩ : FlatIdx H222)
      = 1 := by decide
theorem slot_a10 :
    fin8EquivFlatIdx222.symm (⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, ⟨0, by decide⟩⟩ : FlatIdx H222)
      = 2 := by decide
theorem slot_a11 :
    fin8EquivFlatIdx222.symm (⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, ⟨1, by decide⟩⟩ : FlatIdx H222)
      = 3 := by decide

/-- The `B`-block slots (`s = 1`): `b00=4, b01=5, b10=6, b11=7`. By `decide` (kernel). -/
theorem slot_b00 :
    fin8EquivFlatIdx222.symm (⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨0, by decide⟩⟩ : FlatIdx H222)
      = 4 := by decide
theorem slot_b01 :
    fin8EquivFlatIdx222.symm (⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨1, by decide⟩⟩ : FlatIdx H222)
      = 5 := by decide
theorem slot_b10 :
    fin8EquivFlatIdx222.symm (⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ⟨0, by decide⟩⟩ : FlatIdx H222)
      = 6 := by decide
theorem slot_b11 :
    fin8EquivFlatIdx222.symm (⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ⟨1, by decide⟩⟩ : FlatIdx H222)
      = 7 := by decide

end DLNFibre.DLN.RLCT
