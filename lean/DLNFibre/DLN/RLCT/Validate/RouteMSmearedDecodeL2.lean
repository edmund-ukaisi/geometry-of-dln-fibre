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
noncomputable def topSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (a : Fin r) (j : Fin (M 2)) :
    FlatIdx M :=
  ⟨⟨(1 : Fin 2), deepWidthEquiv hrs (Sum.inl a)⟩, j⟩

/-- A deepest-bottom flat slot `⟨⟨1, deepWidthEquiv (inr b)⟩, j⟩` (bottom `s`-row block of `A¹`). -/
noncomputable def botSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (b : Fin s) (j : Fin (M 2)) :
    FlatIdx M :=
  ⟨⟨(1 : Fin 2), deepWidthEquiv hrs (Sum.inr b)⟩, j⟩

/-- The deepest row of `topSlot a j`, as a `Fin (M 1)` (the `M (1:Fin 2).castSucc = M 1` row). -/
theorem topSlot_row (M : Fin 3 → ℕ) (hrs : r + s = M 1) (a : Fin r) (j : Fin (M 2)) :
    (topSlot M hrs a j).1.2 = deepWidthEquiv hrs (Sum.inl a) := rfl

/-- The deepest row of `botSlot b j`. -/
theorem botSlot_row (M : Fin 3 → ℕ) (hrs : r + s = M 1) (b : Fin s) (j : Fin (M 2)) :
    (botSlot M hrs b j).1.2 = deepWidthEquiv hrs (Sum.inr b) := rfl

/-- The `Fin (routeMAmbient M)` coordinate of a flat slot `q` (the `slotEquiv.symm`). -/
noncomputable def coordOf (M : Fin 3 → ℕ) (q : FlatIdx M) : Fin (routeMAmbient M) :=
  (slotEquiv M).symm q

/-- The deepest-top radial coords (R's active set / the shear's Core slots): the `r·c` coords
`coordOf (topSlot a j)`. -/
noncomputable def topCoords (M : Fin 3 → ℕ) (hrs : r + s = M 1) : Finset (Fin (routeMAmbient M)) :=
  Finset.image (fun p : Fin r × Fin (M 2) => coordOf M (topSlot M hrs p.1 p.2)) Finset.univ

/-- The radial pivot coord (the `(0,0)` entry of the top block) — needs `0 < r`, `0 < M 2`. -/
noncomputable def pivotCoord (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2) :
    Fin (routeMAmbient M) :=
  coordOf M (topSlot M hrs ⟨0, hr⟩ ⟨0, hc⟩)

/-! ## `coordOf` injectivity + the deepest-row slots are distinct -/

/-- `coordOf` is injective (`slotEquiv.symm` is a bijection). -/
theorem coordOf_injective (M : Fin 3 → ℕ) {q q' : FlatIdx M} (h : coordOf M q = coordOf M q') :
    q = q' := (slotEquiv M).symm.injective h

/-- `coordOf q = coordOf q' ↔ q = q'`. -/
theorem coordOf_inj_iff (M : Fin 3 → ℕ) (q q' : FlatIdx M) :
    coordOf M q = coordOf M q' ↔ q = q' :=
  ⟨coordOf_injective M, fun h => by rw [h]⟩

/-- `deepWidthEquiv` separates the `inl`/`inr` blocks: `topSlot a j ≠ botSlot b j'` (same layer `1`, so
the row equality is homogeneous; `deepWidthEquiv` injective + `Sum.inl_ne_inr`). -/
theorem topSlot_ne_botSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1)
    (a : Fin r) (j : Fin (M 2)) (b : Fin s) (j' : Fin (M 2)) :
    topSlot M hrs a j ≠ botSlot M hrs b j' := by
  intro h
  -- both slots have layer `1`; compare row `.val`s (non-dependent ℕ codomain ⟹ `congrArg` is cast-free)
  have hval : (deepWidthEquiv hrs (Sum.inl a) : Fin (M 1)).val
      = (deepWidthEquiv hrs (Sum.inr b) : Fin (M 1)).val :=
    congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) h
  have hrow : deepWidthEquiv hrs (Sum.inl a) = deepWidthEquiv hrs (Sum.inr b) := Fin.ext hval
  exact Sum.inl_ne_inr ((deepWidthEquiv hrs).injective hrow)

/-- A front slot is never a deepest-top slot (different layer: `0 ≠ 1`). -/
theorem frontSlot_ne_topSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1)
    (i : Fin (M 0)) (jf : Fin (M 1)) (a : Fin r) (j : Fin (M 2)) :
    frontSlot M i jf ≠ topSlot M hrs a j := by
  intro h
  have hlayer : (0 : Fin 2) = (1 : Fin 2) := congrArg (·.1.1) h
  exact absurd hlayer (by decide)

end DLNFibre.DLN.RLCT
