import DLNFibre.DLN.RLCT.Validate.RouteMSmearedChartOpaque
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP

/-!
# `RouteMSmearedDecodeL2` — the opaque-width L=2 chart maps `ψ`/`R` + the DECODE

The opaque-width generalization of the `(2,3,1)` chart (`RouteM231Smeared`). Builds, for any L=2 widths
`M : Fin 3 → ℕ` with the front-bottleneck split `r + s = M 1`:

* the slot bijection `slotEquiv M : Fin (routeMAmbient M) ≃ FlatIdx M` (the noncomputable `equivFin.symm`);
* the deepest-top flat coords `topSlot a j` / bottom coords `botSlot b j` (via `deepWidthEquiv hrs`);
* the radial pivot `pivotSlot`, the radial blow-up `R := pivotBlowupOn (topCoords) pivotSlot`;
* the chart components read off `u` at these slots (`A0u`, `zu`, `HbarUnit u`, `Sbotu`, `Λ₀u`);
* the shear `shiftCore` (the `−Λ₀·Sbot` shift into the Core slots) + `ψ := paramsEquivFlat ∘ packM ∘ shearMBody`;
* the DECODE `packM (shearMBody (R u)) = chartL2Params M hrs (A0u u) (zu u) (HbarUnit u) (Sbotu u) (Λ₀u u)`.

Then the banked `routeMCore_phiL2` gives the rate `routeMCore M (ψ (R u)) = (zu u)²·‖P₁·H̄_unit‖²` off the
shear pole, the input to `routeMCore_box_diverges_smearedL2`'s peeled-rate hypothesis.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin 3 → ℕ} {r s : ℕ}

/-! ## The slot bijection and the deepest-row flat coords -/

/-- The (noncomputable) slot bijection `Fin (routeMAmbient M) ≃ FlatIdx M` (the `equivFin.symm`;
`routeMAmbient M = flatDim M = card (FlatIdx M)`). -/
noncomputable def slotEquiv (M : Fin 3 → ℕ) : Fin (routeMAmbient M) ≃ FlatIdx M :=
  (Fintype.equivFin (FlatIdx M)).symm

/-- A layer-0 (front) flat slot `⟨⟨0, i⟩, j⟩`. -/
def frontSlot (M : Fin 3 → ℕ) (i : Fin (M 0)) (j : Fin (M 1)) : FlatIdx M :=
  ⟨⟨(0 : Fin 2), i⟩, j⟩

/-- A deepest-top flat slot `⟨⟨1, deepWidthEquiv (inl a)⟩, j⟩` (top `r`-row block of `A¹`). -/
def topSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (a : Fin r) (j : Fin (M 2)) : FlatIdx M :=
  ⟨⟨(1 : Fin 2), deepWidthEquiv hrs (Sum.inl a)⟩, j⟩

/-- A deepest-bottom flat slot `⟨⟨1, deepWidthEquiv (inr b)⟩, j⟩` (bottom `s`-row block of `A¹`). -/
def botSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (b : Fin s) (j : Fin (M 2)) : FlatIdx M :=
  ⟨⟨(1 : Fin 2), deepWidthEquiv hrs (Sum.inr b)⟩, j⟩

end DLNFibre.DLN.RLCT
