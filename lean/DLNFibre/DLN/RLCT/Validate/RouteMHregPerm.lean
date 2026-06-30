import DLNFibre.DLN.RLCT.Validate.RouteMHDtotEihd
import DLNFibre.DLN.RLCT.Validate.RouteMTwoSidedReg

/-!
# `RouteMHregPerm` — the `hreg` regauge abs-det-`1` via the coordinate-permutation route

The two-sided staircase keystone (`RouteMHDtotEihd.interiorDet_leaf_headline_eihd`) carries the single
volume hypothesis `hreg : |det ((eihdOut ha).symm ∘ₗ (eIn ha))| = 1`. The naive
`MeasurePreserving`-factor route is BLOCKED: the intermediate `StairProd (eihdV M) 2` (a nested product
of `SchurInc`/matrix-pair spaces) has no `MeasureSpace`, so one cannot chain `MeasurePreserving` through
it.

Route taken: the regauge composite `(eihdOut ha).symm ∘ₗ (eIn ha)` is an endomorphism of the FLAT space
`Fin (flatDim M) → ℝ`, and EVERY constituent of `eIn`/`eihdOut` is a coordinate bijection on `→ℝ`
spaces (`funCongrLeft`/`piCurry`/`piFinTwo`/`sumArrowLequivProdArrow`/`curry`/`ofLinearEquiv`/
`reindexLinearEquiv`/`prodComm`/`prodCongr`/`prodUnique`, plus the hand-rolled `roleReorderLE`/
`eInRearrange`). So the composite is `funCongrLeft ℝ ℝ σ` for some index permutation `σ : Fin (flatDim M)
≃ Fin (flatDim M)` — never named explicitly. `funCongrLeft ℝ ℝ σ` is measure-preserving (it is the
`MeasurableEquiv.arrowCongr' σ.symm (.refl ℝ)` precomposition, volume-preserving by
`volume_preserving_arrowCongr'`), which discharges `hreg` through the banked
`hreg_of_measurePreserving_comp`.

The σ-existence is proved STRUCTURALLY (Codex xhigh route B): a predicate `IsCoordLE` ("this LinearEquiv
is `funCongrLeft`-conjugate relative to chosen `→ℝ` charts on its endpoints") closed under `trans`/`symm`/
`prodCongr`, certified on each atom. This avoids enumerating the nested `Σ/⊕/Fin`-product σ over the
opaque K-core widths.

Axiom-clean `[propext, Classical.choice, Quot.sound]` target.
-/

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace DLNFibre.DLN.RLCT

universe u v w

/-! ## The finish: a `funCongrLeft σ` self-map of the flat space has abs-det `1` -/

/-- **`funCongrLeft ℝ ℝ σ` is measure-preserving** on `Fin N → ℝ` (`σ : Fin N ≃ Fin N`). As a function
it is `(· ∘ σ) = MeasurableEquiv.arrowCongr' σ.symm (.refl ℝ)`, volume-preserving by
`volume_preserving_arrowCongr'`. -/
theorem measurePreserving_funCongrLeft {N : ℕ} (σ : Fin N ≃ Fin N) :
    MeasurePreserving ((LinearEquiv.funCongrLeft ℝ ℝ σ : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ)) :
        (Fin N → ℝ) → (Fin N → ℝ))
      (volume : Measure (Fin N → ℝ)) volume := by
  have hmp : MeasurePreserving
      (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ))
      (volume : Measure (Fin N → ℝ)) volume :=
    volume_preserving_arrowCongr' σ.symm (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  -- the two underlying functions agree: both are `f ↦ f ∘ σ`
  have hfun : ((LinearEquiv.funCongrLeft ℝ ℝ σ : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ)) :
        (Fin N → ℝ) → (Fin N → ℝ))
      = (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ) :
          (Fin N → ℝ) → (Fin N → ℝ)) := by
    funext f
    rfl
  rw [hfun]; exact hmp

/-- **The regauge `hreg` from an existential `funCongrLeft` form.** If the flat-space composite
`eOut.symm ∘ₗ eIn` equals `funCongrLeft ℝ ℝ σ` for some `σ`, then `|det| = 1` (the composite is the
measure-preserving coordinate permutation `funCongrLeft σ`, fed through `hreg_of_measurePreserving_comp`). -/
theorem hreg_of_exists_funCongrLeft {N n : ℕ}
    (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (eIn eOut : (Fin N → ℝ) ≃ₗ[ℝ] StairProd V n)
    (hσ : ∃ σ : Fin N ≃ Fin N,
      ((eOut.symm : StairProd V n →ₗ[ℝ] (Fin N → ℝ))
          ∘ₗ (eIn : (Fin N → ℝ) →ₗ[ℝ] StairProd V n))
        = ((LinearEquiv.funCongrLeft ℝ ℝ σ : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ)) :
            (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) :
    |LinearMap.det ((eOut.symm : StairProd V n →ₗ[ℝ] (Fin N → ℝ))
        ∘ₗ (eIn : (Fin N → ℝ) →ₗ[ℝ] StairProd V n))| = 1 := by
  obtain ⟨σ, hσ⟩ := hσ
  refine hreg_of_measurePreserving_comp V eIn eOut ?_
  rw [hσ]
  exact measurePreserving_funCongrLeft σ

/-! ## `IsCoordLE` — "this `LinearEquiv` is a coordinate permutation relative to `→ℝ` charts"

For a `LinearEquiv e : X ≃ₗ Y` with `→ℝ` charts `cx : X ≃ₗ (ι → ℝ)`, `cy : Y ≃ₗ (κ → ℝ)`, the predicate
says the chart-conjugate `cy ∘ e ∘ cx.symm` is `funCongrLeft ℝ ℝ σ` for some index equiv `σ : κ ≃ ι`.
Closed under `trans` (compose σ's contravariantly) and `symm`. The whole `eIn ≪≫ₗ eOut.symm` chain
factors through this with the flat chart `LinearEquiv.refl` at both endpoints. -/

/-- **`IsCoordLE cx cy e`** — the chart-conjugate `cx.symm ≪≫ₗ e ≪≫ₗ cy : (ι → ℝ) ≃ₗ (κ → ℝ)` equals
`funCongrLeft σ` for some `σ : κ ≃ ι` (as a `LinearEquiv`). The charts `cx`/`cy` pin the `→ℝ`
coordinatizations of the endpoints. -/
def IsCoordLE {X Y : Type*} {ι κ : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (cx : X ≃ₗ[ℝ] (ι → ℝ)) (cy : Y ≃ₗ[ℝ] (κ → ℝ)) (e : X ≃ₗ[ℝ] Y) : Prop :=
  ∃ σ : κ ≃ ι, (cx.symm ≪≫ₗ e ≪≫ₗ cy) = LinearEquiv.funCongrLeft ℝ ℝ σ

/-- The identity is a coordinate permutation (σ = `refl`, the conjugate `cx.symm ≪≫ₗ cx = refl`). -/
theorem IsCoordLE.refl {X ι : Type*} [AddCommGroup X] [Module ℝ X]
    (cx : X ≃ₗ[ℝ] (ι → ℝ)) :
    IsCoordLE cx cx (LinearEquiv.refl ℝ X) := by
  refine ⟨Equiv.refl ι, ?_⟩
  rw [LinearEquiv.funCongrLeft_id]
  ext f i
  simp only [LinearEquiv.trans_apply, LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply]

/-- **`IsCoordLE` is closed under `trans`** (shared middle chart `cy`): compose the index permutations
`σ₁ : κ ≃ ι`, `σ₂ : μ ≃ κ` to `σ₂.trans σ₁ : μ ≃ ι`. -/
theorem IsCoordLE.trans {X Y Z : Type*} {ι κ μ : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
    {cx : X ≃ₗ[ℝ] (ι → ℝ)} {cy : Y ≃ₗ[ℝ] (κ → ℝ)} {cz : Z ≃ₗ[ℝ] (μ → ℝ)}
    {e₁ : X ≃ₗ[ℝ] Y} {e₂ : Y ≃ₗ[ℝ] Z}
    (h₁ : IsCoordLE cx cy e₁) (h₂ : IsCoordLE cy cz e₂) :
    IsCoordLE cx cz (e₁ ≪≫ₗ e₂) := by
  obtain ⟨σ₁, hσ₁⟩ := h₁
  obtain ⟨σ₂, hσ₂⟩ := h₂
  refine ⟨σ₂.trans σ₁, ?_⟩
  -- conjugate of e₁ ≪≫ₗ e₂ factors as (conj of e₁) ≪≫ₗ (conj of e₂) via cy ≪≫ₗ cy.symm = refl
  have key : (cx.symm ≪≫ₗ (e₁ ≪≫ₗ e₂) ≪≫ₗ cz)
      = ((cx.symm ≪≫ₗ e₁ ≪≫ₗ cy) ≪≫ₗ (cy.symm ≪≫ₗ e₂ ≪≫ₗ cz)) := by
    ext f i
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [key, hσ₁, hσ₂, ← LinearEquiv.funCongrLeft_comp]

/-- **`IsCoordLE` is closed under `symm`** (swap charts; invert the index permutation). -/
theorem IsCoordLE.symm {X Y : Type*} {ι κ : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {cx : X ≃ₗ[ℝ] (ι → ℝ)} {cy : Y ≃ₗ[ℝ] (κ → ℝ)} {e : X ≃ₗ[ℝ] Y}
    (h : IsCoordLE cx cy e) :
    IsCoordLE cy cx e.symm := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, ?_⟩
  -- the conjugate of e.symm is the symm of the conjugate of e = (funCongrLeft σ).symm = funCongrLeft σ.symm
  have hconj : (cy.symm ≪≫ₗ e.symm ≪≫ₗ cx) = (cx.symm ≪≫ₗ e ≪≫ₗ cy).symm := by
    ext g; rfl
  rw [hconj, hσ, LinearEquiv.funCongrLeft_symm]

/-! ## The `→ℝ` charts on the building-block spaces -/

/-- The product chart `(X × Y) ≃ₗ (ι ⊕ κ → ℝ)` from charts on the factors (via
`sumArrowLequivProdArrow.symm`). -/
def prodChart {X Y : Type*} {ι κ : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (cx : X ≃ₗ[ℝ] (ι → ℝ)) (cy : Y ≃ₗ[ℝ] (κ → ℝ)) :
    (X × Y) ≃ₗ[ℝ] (ι ⊕ κ → ℝ) :=
  (cx.prodCongr cy) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow ι κ ℝ ℝ).symm

/-! ## The atom certificates -/

/-- **Atom: `funCongrLeft e.symm` is a coordinate permutation** (flat charts both sides; σ = e.symm). -/
theorem isCoordLE_funCongrLeft {ι κ : Type*} (e : ι ≃ κ) :
    IsCoordLE (LinearEquiv.refl ℝ (ι → ℝ)) (LinearEquiv.refl ℝ (κ → ℝ))
      (LinearEquiv.funCongrLeft ℝ ℝ e.symm) := by
  refine ⟨e.symm, ?_⟩
  ext f i
  simp only [LinearEquiv.trans_apply, LinearEquiv.refl_apply, LinearEquiv.refl_symm]

/-- **Atom: `prodCongr e₁ e₂` is a coordinate permutation** (product charts; σ = `sumCongr`). -/
theorem isCoordLE_prodCongr {X₁ Y₁ X₂ Y₂ : Type*} {ι₁ κ₁ ι₂ κ₂ : Type*}
    [AddCommGroup X₁] [Module ℝ X₁] [AddCommGroup Y₁] [Module ℝ Y₁]
    [AddCommGroup X₂] [Module ℝ X₂] [AddCommGroup Y₂] [Module ℝ Y₂]
    {cx₁ : X₁ ≃ₗ[ℝ] (ι₁ → ℝ)} {cy₁ : Y₁ ≃ₗ[ℝ] (κ₁ → ℝ)}
    {cx₂ : X₂ ≃ₗ[ℝ] (ι₂ → ℝ)} {cy₂ : Y₂ ≃ₗ[ℝ] (κ₂ → ℝ)}
    {e₁ : X₁ ≃ₗ[ℝ] Y₁} {e₂ : X₂ ≃ₗ[ℝ] Y₂}
    (h₁ : IsCoordLE cx₁ cy₁ e₁) (h₂ : IsCoordLE cx₂ cy₂ e₂) :
    IsCoordLE (prodChart cx₁ cx₂) (prodChart cy₁ cy₂) (e₁.prodCongr e₂) := by
  obtain ⟨σ₁, hσ₁⟩ := h₁
  obtain ⟨σ₂, hσ₂⟩ := h₂
  refine ⟨Equiv.sumCongr σ₁ σ₂, ?_⟩
  -- conjugate of e₁.prodCongr e₂ = funCongrLeft (sumCongr σ₁ σ₂); check on a sum index
  ext f i
  rcases i with a | b
  · -- the inl component: reads through cx₁/cy₁/e₁ — i.e. `(conj of e₁) (f ∘ inl)` at index a
    have hcomp := LinearEquiv.ext_iff.mp hσ₁ (fun b => f (Sum.inl b))
    have hval := congrFun hcomp a
    simp only [prodChart, LinearEquiv.trans_apply, LinearEquiv.symm_symm, LinearEquiv.prodCongr_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.sumCongr_apply,
      Sum.map_inl] at hval ⊢
    exact hval
  · have hcomp := LinearEquiv.ext_iff.mp hσ₂ (fun a => f (Sum.inr a))
    have hval := congrFun hcomp b
    simp only [prodChart, LinearEquiv.trans_apply, LinearEquiv.symm_symm, LinearEquiv.prodCongr_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.sumCongr_apply,
      Sum.map_inr] at hval ⊢
    exact hval

/-! ## The `read-form` atom: a coordinate-reading LinearEquiv is `IsCoordLE`

The most uniform atom: a LinearEquiv `e : X ≃ₗ Y` whose chart-conjugate reads each output coordinate
from a single input coordinate (`(cy (e (cx.symm f))) k = f (τ k)`, `τ` bijective) is `IsCoordLE`.
Every constituent reshape of `eIn`/`eihdOut` is coordinate-reading; the bijective `τ` IS the σ. -/

/-- **The read-form atom.** If the chart-conjugate of `e` reads output coord `k` from input coord
`σ.symm k` (`σ : κ ≃ ι`), then `IsCoordLE cx cy e` with that `σ`. -/
theorem isCoordLE_of_read {X Y : Type*} {ι κ : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {cx : X ≃ₗ[ℝ] (ι → ℝ)} {cy : Y ≃ₗ[ℝ] (κ → ℝ)} {e : X ≃ₗ[ℝ] Y}
    (σ : κ ≃ ι)
    (hread : ∀ (f : ι → ℝ) (k : κ), cy (e (cx.symm f)) k = f (σ k)) :
    IsCoordLE cx cy e := by
  refine ⟨σ, ?_⟩
  ext f k
  rw [show ((cx.symm ≪≫ₗ e ≪≫ₗ cy) f) k = cy (e (cx.symm f)) k from rfl, hread f k]
  rfl

/-! ## `→ℝ` charts on the `eihdV`/`StairProd`/`Params` spaces (for the L=2 `eihd` two-sided staircase)

The composite `eihdOut.symm ∘ₗ eIn` factors as `eIn ≪≫ₗ packStair.symm ≪≫ₗ paramsEquivFlatLinear`
(unfolding `eihdOut`). Charts: `refl` on the flat ends, `paramsEquivFlatLinear` on `Params`, and an
explicit `stairChart` on `StairProd (eihdV M) 2` built from the matrix flattenings `flatMatLE.symm`.
Each piece is then certified `IsCoordLE` (the σ-existence assembled by `IsCoordLE.trans`/`.symm`). -/

section L2

variable {M : Fin (2 + 1) → ℕ}

/-- The matrix flattening chart `Matrix (Fin a) (Fin b) ℝ ≃ₗ (Fin (a*b) → ℝ)` (`flatMatLE.symm`). -/
def matChart (a b : ℕ) : Matrix (Fin a) (Fin b) ℝ ≃ₗ[ℝ] (Fin (a * b) → ℝ) := (flatMatLE a b).symm

/-- The `PUnit ≃ₗ (Fin 0 → ℝ)` chart (both subsingletons). -/
def punitChart : PUnit ≃ₗ[ℝ] (Fin 0 → ℝ) where
  toFun := fun _ => fun i => i.elim0
  invFun := fun _ => PUnit.unit
  map_add' := fun _ _ => by funext i; exact i.elim0
  map_smul' := fun _ _ => by funext i; exact i.elim0
  left_inv := fun _ => rfl
  right_inv := fun _ => by funext i; exact i.elim0

/-- The chart on `eihdV M 0 = SchurInc (t,r,c)` to a 4-fold sum index. -/
def v0Chart (M : Fin (2 + 1) → ℕ) :
    eihdV M 0 ≃ₗ[ℝ]
      ((Fin (schurT1 M * schurT1 M) ⊕ (Fin (schurT1 M * schurC1 M) ⊕
        (Fin (schurR1 M * schurT1 M) ⊕ Fin (schurR1 M * schurC1 M)))) → ℝ) :=
  prodChart (matChart (schurT1 M) (schurT1 M))
    (prodChart (matChart (schurT1 M) (schurC1 M))
      (prodChart (matChart (schurR1 M) (schurT1 M)) (matChart (schurR1 M) (schurC1 M))))

/-- The chart on `eihdV M 1 = (W, leaf)` matrix pair to a 2-fold sum index. -/
def v1Chart (M : Fin (2 + 1) → ℕ) :
    eihdV M 1 ≃ₗ[ℝ]
      ((Fin (schurC1 M * Wext M 2) ⊕ Fin (schurT1 M * Wext M 2)) → ℝ) :=
  prodChart (matChart (schurC1 M) (Wext M 2)) (matChart (schurT1 M) (Wext M 2))

/-- The chart on `StairProd (eihdV M) 2 = V0 × (V1 × PUnit)`. -/
def stairChart (M : Fin (2 + 1) → ℕ) :
    StairProd (eihdV M) 2 ≃ₗ[ℝ]
      (((Fin (schurT1 M * schurT1 M) ⊕ (Fin (schurT1 M * schurC1 M) ⊕
          (Fin (schurR1 M * schurT1 M) ⊕ Fin (schurR1 M * schurC1 M)))) ⊕
        (((Fin (schurC1 M * Wext M 2) ⊕ Fin (schurT1 M * Wext M 2)) ⊕ Fin 0))) → ℝ) :=
  prodChart (v0Chart M) (prodChart (v1Chart M) punitChart)

/-! ## `prodChart` evaluation lemmas (read a `prodChart` at an `inl`/`inr` index) -/

/-- `prodChart` at an `inl` index reads the first factor's chart. -/
theorem prodChart_apply_inl {X Y : Type*} {ι κ : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (cx : X ≃ₗ[ℝ] (ι → ℝ)) (cy : Y ≃ₗ[ℝ] (κ → ℝ)) (p : X × Y) (a : ι) :
    prodChart cx cy p (Sum.inl a) = cx p.1 a := rfl

/-- `prodChart` at an `inr` index reads the second factor's chart. -/
theorem prodChart_apply_inr {X Y : Type*} {ι κ : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (cx : X ≃ₗ[ℝ] (ι → ℝ)) (cy : Y ≃ₗ[ℝ] (κ → ℝ)) (p : X × Y) (b : κ) :
    prodChart cx cy p (Sum.inr b) = cy p.2 b := rfl

/-- `matChart` reads matrix entry at the `finProdFinEquiv.symm`-unpacked index. -/
theorem matChart_apply (a b : ℕ) (Mat : Matrix (Fin a) (Fin b) ℝ) (m : Fin (a * b)) :
    matChart a b Mat m = Mat (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2 := by
  have hfm : flatMatLE a b (matChart a b Mat) = Mat := by
    rw [matChart]; exact (flatMatLE a b).apply_symm_apply Mat
  have hentry : flatMatLE a b (matChart a b Mat)
        (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2
      = Mat (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2 := by rw [hfm]
  rw [flatMatLE_apply] at hentry
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using hentry

/-! ## The `eIn` block reads (each output block of `eIn ha` reads one flat coordinate) -/

/-- The V0-K block read: `((eIn ha δ).1).1 i j` is the K-slot flat coord. -/
theorem eIn_readK (ha : StructAdm M (tach M)) (δ : Fin (flatDim M) → ℝ)
    (i j : Fin (schurT1 M)) :
    ((eIn ha δ).1).1 i j
      = δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
          ⟨0, Sum.inl ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
            (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, j))))))⟩) := by
  rw [show ((eIn ha δ).1) = frameToSchurInc ha
      (fun a => δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨0, Sum.inl a⟩))
    from rfl, frameToSchurInc_blocks ha]
  rfl

/-- The V0-N block read. -/
theorem eIn_readN (ha : StructAdm M (tach M)) (δ : Fin (flatDim M) → ℝ)
    (i : Fin (schurT1 M)) (j : Fin (schurC1 M)) :
    ((eIn ha δ).1).2.1 i j
      = δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
          ⟨0, Sum.inl ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
            (Sum.inl (Sum.inr (finProdFinEquiv (i, j)))))⟩) := by
  rw [show ((eIn ha δ).1) = frameToSchurInc ha
      (fun a => δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨0, Sum.inl a⟩))
    from rfl, frameToSchurInc_blocks ha]
  rfl

/-- The V0-X block read. -/
theorem eIn_readX (ha : StructAdm M (tach M)) (δ : Fin (flatDim M) → ℝ)
    (i : Fin (schurR1 M)) (j : Fin (schurT1 M)) :
    ((eIn ha δ).1).2.2.1 i j
      = δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
          ⟨0, Sum.inl ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
            (Sum.inl (Sum.inl (Sum.inr (finProdFinEquiv (i, j))))))⟩) := by
  rw [show ((eIn ha δ).1) = frameToSchurInc ha
      (fun a => δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨0, Sum.inl a⟩))
    from rfl, frameToSchurInc_blocks ha]
  rfl

/-- The V0-E block read. -/
theorem eIn_readE (ha : StructAdm M (tach M)) (δ : Fin (flatDim M) → ℝ)
    (i : Fin (schurR1 M)) (j : Fin (schurC1 M)) :
    ((eIn ha δ).1).2.2.2 i j
      = δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
          ⟨0, Sum.inl ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
            (Sum.inr (finProdFinEquiv (i, j))))⟩) := by
  rw [show ((eIn ha δ).1) = frameToSchurInc ha
      (fun a => δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨0, Sum.inl a⟩))
    from rfl, frameToSchurInc_blocks ha]
  rfl

/-- The V1-W block read (boundary-0 lift slot). -/
theorem eIn_readW (ha : StructAdm M (tach M)) (δ : Fin (flatDim M) → ℝ)
    (i : Fin (schurC1 M)) (j : Fin (Wext M 2)) :
    (eIn ha δ).2.1.1 i j
      = δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
          ⟨0, Sum.inr ((liftSlotEquiv M (tDesc M (tach M)) 0 (by decide)).symm (i, j))⟩) := by
  show (wToMat ha (fun a => δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
      ⟨0, Sum.inr a⟩)) i j) = _
  rw [wToMat]
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    prodMatLE, Matrix.coe_ofLinearEquiv, Matrix.of_apply, Equiv.apply_symm_apply]
  rfl

/-- The V1-leaf block read (boundary-1 frame slot). -/
theorem eIn_readLeaf (ha : StructAdm M (tach M)) (δ : Fin (flatDim M) → ℝ)
    (i : Fin (schurT1 M)) (j : Fin (Wext M 2)) :
    (eIn ha δ).2.1.2 i j
      = δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
          ⟨1, Sum.inl (finProdFinEquiv (i, j))⟩) :=
  flatMatLE_apply (schurT1 M) (Wext M 2)
    (fun a => δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨1, Sum.inl a⟩)) i j

/-! ## The `eIn` coordinate-permutation certificate

`σ_eIn : BigIdx ≃ Fin (flatDim M)` is `(bigToChartEin) ≪≫ chartIdxEquiv.symm`, where `bigToChartEin :
BigIdx ≃ ChartIdx` reassembles each `stairChart` block index into its `chartIdxEquiv` slot:
the four V0 roles via `frameSplitEquiv.symm` (after the `knxeReshuffle` `KNXE → ((KX)N)E`), the V1-W
block via `liftSlotEquiv.symm`, the V1-leaf block as the boundary-1 frame slot. -/

/-- The V0 role-sum reshuffle `K⊕(N⊕(X⊕E)) → ((K⊕X)⊕N)⊕E` (the `frameSplitEquiv` input order, vs the
`stairChart` `roleReorderLE` output order). -/
def knxeReshuffle (M : Fin (2 + 1) → ℕ) :
    (Fin (schurT1 M * schurT1 M) ⊕ (Fin (schurT1 M * schurC1 M) ⊕
        (Fin (schurR1 M * schurT1 M) ⊕ Fin (schurR1 M * schurC1 M))))
      ≃ (((Fin (schurT1 M * schurT1 M) ⊕ Fin (schurR1 M * schurT1 M)) ⊕ Fin (schurT1 M * schurC1 M))
          ⊕ Fin (schurR1 M * schurC1 M)) where
  toFun := fun x => match x with
    | Sum.inl mK => Sum.inl (Sum.inl (Sum.inl mK))
    | Sum.inr (Sum.inl mN) => Sum.inl (Sum.inr mN)
    | Sum.inr (Sum.inr (Sum.inl mX)) => Sum.inl (Sum.inl (Sum.inr mX))
    | Sum.inr (Sum.inr (Sum.inr mE)) => Sum.inr mE
  invFun := fun y => match y with
    | Sum.inl (Sum.inl (Sum.inl mK)) => Sum.inl mK
    | Sum.inl (Sum.inr mN) => Sum.inr (Sum.inl mN)
    | Sum.inl (Sum.inl (Sum.inr mX)) => Sum.inr (Sum.inr (Sum.inl mX))
    | Sum.inr mE => Sum.inr (Sum.inr (Sum.inr mE))
  left_inv := fun x => by rcases x with _ | _ | _ | _ <;> rfl
  right_inv := fun y => by rcases y with ((_ | _) | _) | _ <;> rfl

/-- `bigToChartEin : BigIdx ≃ ChartIdx` — the index-level inverse of the `eIn` reshape. -/
def bigToChartEin (ha : StructAdm M (tach M)) :
    (((Fin (schurT1 M * schurT1 M) ⊕ (Fin (schurT1 M * schurC1 M) ⊕
        (Fin (schurR1 M * schurT1 M) ⊕ Fin (schurR1 M * schurC1 M)))) ⊕
        (((Fin (schurC1 M * Wext M 2) ⊕ Fin (schurT1 M * Wext M 2)) ⊕ Fin 0))))
      ≃ ChartIdx M (tDesc M (tach M)) where
  toFun := fun x => match x with
    | Sum.inl v0 =>
      ⟨0, Sum.inl ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
        (knxeReshuffle M v0))⟩
    | Sum.inr (Sum.inl (Sum.inl mW)) =>
      ⟨0, Sum.inr ((liftSlotEquiv M (tDesc M (tach M)) 0 (by decide)).symm
        (finProdFinEquiv.symm mW))⟩
    | Sum.inr (Sum.inl (Sum.inr mL)) => ⟨1, Sum.inl mL⟩
    | Sum.inr (Sum.inr e) => e.elim0
  invFun := fun c => match c with
    | ⟨⟨0, _⟩, Sum.inl s⟩ =>
      Sum.inl ((knxeReshuffle M).symm
        ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)) s))
    | ⟨⟨0, _⟩, Sum.inr s⟩ =>
      Sum.inr (Sum.inl (Sum.inl (finProdFinEquiv ((liftSlotEquiv M (tDesc M (tach M)) 0 (by decide)) s))))
    | ⟨⟨1, _⟩, Sum.inl s⟩ => Sum.inr (Sum.inl (Sum.inr s))
    | ⟨⟨1, _⟩, Sum.inr s⟩ => (by rw [liftDim_one_eq_zero] at s; exact s.elim0)
  left_inv := fun x => by
    rcases x with v0 | (mW | mL) | e
    · show Sum.inl ((knxeReshuffle M).symm ((frameSplitEquiv M (tach M) 1 _ _)
          ((frameSplitEquiv M (tach M) 1 _ _).symm (knxeReshuffle M v0)))) = _
      simp
    · have h1 : (liftSlotEquiv M (tDesc M (tach M)) 0 (by decide))
          ((liftSlotEquiv M (tDesc M (tach M)) 0 (by decide)).symm (finProdFinEquiv.symm mW))
          = finProdFinEquiv.symm mW := Equiv.apply_symm_apply _ _
      show Sum.inr (Sum.inl (Sum.inl (finProdFinEquiv ((liftSlotEquiv M (tDesc M (tach M)) 0 _)
          ((liftSlotEquiv M (tDesc M (tach M)) 0 _).symm (finProdFinEquiv.symm mW)))))) = _
      rw [h1]
      exact congrArg (fun z => Sum.inr (Sum.inl (Sum.inl z))) (Equiv.apply_symm_apply _ mW)
    · rfl
    · exact e.elim0
  right_inv := fun c => by
    obtain ⟨⟨kv, hk⟩, s⟩ := c
    match kv, hk, s with
    | 0, _, Sum.inl s =>
      have h1 : knxeReshuffle M ((knxeReshuffle M).symm
            ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)) s))
          = (frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)) s :=
          Equiv.apply_symm_apply _ _
      show (⟨0, Sum.inl ((frameSplitEquiv M (tach M) 1 _ _).symm
          (knxeReshuffle M ((knxeReshuffle M).symm
            ((frameSplitEquiv M (tach M) 1 _ _) s))))⟩ : ChartIdx M (tDesc M (tach M)))
          = ⟨0, Sum.inl s⟩
      rw [h1, Equiv.symm_apply_apply]
    | 0, _, Sum.inr s =>
      have h1 : finProdFinEquiv.symm (finProdFinEquiv ((liftSlotEquiv M (tDesc M (tach M)) 0
            (by decide)) s)) = (liftSlotEquiv M (tDesc M (tach M)) 0 (by decide)) s :=
          Equiv.symm_apply_apply _ _
      show (⟨0, Sum.inr ((liftSlotEquiv M (tDesc M (tach M)) 0 _).symm
          (finProdFinEquiv.symm (finProdFinEquiv ((liftSlotEquiv M (tDesc M (tach M)) 0 _) s))))⟩ :
            ChartIdx M (tDesc M (tach M))) = ⟨0, Sum.inr s⟩
      rw [h1, Equiv.symm_apply_apply]
    | 1, _, Sum.inl s => rfl
    | 1, _, Sum.inr s => rw [liftDim_one_eq_zero] at s; exact s.elim0

/-- **`eIn ha` is a coordinate permutation** — `IsCoordLE refl (stairChart M) (eIn ha)`, with
`σ = bigToChartEin ≪≫ chartIdxEquiv.symm`. The read is the per-block `eIn_read*` lemmas through the
`prodChart`/`matChart` evaluation. -/
theorem isCoordLE_eIn (ha : StructAdm M (tach M)) :
    IsCoordLE (LinearEquiv.refl ℝ (Fin (flatDim M) → ℝ)) (stairChart M) (eIn ha) := by
  refine isCoordLE_of_read
    ((bigToChartEin ha).trans (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm) ?_
  intro f k
  rw [show (LinearEquiv.refl ℝ (Fin (flatDim M) → ℝ)).symm f = f from rfl]
  rcases k with v0 | (mW | mL) | e
  · -- V0: rcases the 4 roles
    rcases v0 with mK | mN | mX | mE
    · rw [show stairChart M (eIn ha f) (Sum.inl (Sum.inl mK)) = ((eIn ha f).1).1
            (finProdFinEquiv.symm mK).1 (finProdFinEquiv.symm mK).2 from
          matChart_apply (schurT1 M) (schurT1 M) (((eIn ha f).1).1) mK
        , eIn_readK]
      simp only [Equiv.trans_apply, Prod.mk.eta, Equiv.apply_symm_apply]
      rfl
    · rw [show stairChart M (eIn ha f) (Sum.inl (Sum.inr (Sum.inl mN))) = ((eIn ha f).1).2.1
            (finProdFinEquiv.symm mN).1 (finProdFinEquiv.symm mN).2 from
          matChart_apply (schurT1 M) (schurC1 M) (((eIn ha f).1).2.1) mN
        , eIn_readN]
      simp only [Equiv.trans_apply, Prod.mk.eta, Equiv.apply_symm_apply]
      rfl
    · rw [show stairChart M (eIn ha f) (Sum.inl (Sum.inr (Sum.inr (Sum.inl mX)))) = ((eIn ha f).1).2.2.1
            (finProdFinEquiv.symm mX).1 (finProdFinEquiv.symm mX).2 from
          matChart_apply (schurR1 M) (schurT1 M) (((eIn ha f).1).2.2.1) mX
        , eIn_readX]
      simp only [Equiv.trans_apply, Prod.mk.eta, Equiv.apply_symm_apply]
      rfl
    · rw [show stairChart M (eIn ha f) (Sum.inl (Sum.inr (Sum.inr (Sum.inr mE)))) = ((eIn ha f).1).2.2.2
            (finProdFinEquiv.symm mE).1 (finProdFinEquiv.symm mE).2 from
          matChart_apply (schurR1 M) (schurC1 M) (((eIn ha f).1).2.2.2) mE
        , eIn_readE]
      simp only [Equiv.trans_apply, Prod.mk.eta, Equiv.apply_symm_apply]
      rfl
  · -- V1-W
    rw [show stairChart M (eIn ha f) (Sum.inr (Sum.inl (Sum.inl mW))) = (eIn ha f).2.1.1
          (finProdFinEquiv.symm mW).1 (finProdFinEquiv.symm mW).2 from
        matChart_apply (schurC1 M) (Wext M 2) ((eIn ha f).2.1.1) mW
      , eIn_readW]
    simp only [Equiv.trans_apply, Prod.mk.eta, Equiv.apply_symm_apply]
    rfl
  · -- V1-leaf
    rw [show stairChart M (eIn ha f) (Sum.inr (Sum.inl (Sum.inr mL))) = (eIn ha f).2.1.2
          (finProdFinEquiv.symm mL).1 (finProdFinEquiv.symm mL).2 from
        matChart_apply (schurT1 M) (Wext M 2) ((eIn ha f).2.1.2) mL
      , eIn_readLeaf]
    show f ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
        ⟨1, Sum.inl (finProdFinEquiv (finProdFinEquiv.symm mL))⟩) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · -- empty
    exact e.elim0

/-! ## The two coordinate-permutation certificates and the assembled `eihd_hreg`

The composite `eihdOut.symm ∘ₗ eIn` corresponds (as a `LinearEquiv`) to
`eIn ha ≪≫ₗ (eihdOut ha).symm`, which factors as `eIn ha ≪≫ₗ (packStair ha).symm ≪≫ₗ
paramsEquivFlatLinear M` (unfolding `eihdOut`). With the flat charts `refl` at the ends, the chart
`paramsEquivFlatLinear M` on `Params`, and `stairChart M` on `StairProd`, each factor is a coordinate
permutation:
* `eIn ha` — `IsCoordLE refl (stairChart M) (eIn ha)`;
* `(packStair ha).symm` — `IsCoordLE.symm` of `IsCoordLE (paramsEquivFlatLinear) (stairChart) (packStair ha)`;
* `paramsEquivFlatLinear M` — `IsCoordLE (paramsEquivFlatLinear) refl (paramsEquivFlatLinear M)` (trivial).
`IsCoordLE.trans` composes them to `IsCoordLE refl refl (eIn ha ≪≫ₗ (eihdOut ha).symm)`, i.e. the
`∃ σ, … = funCongrLeft σ` that `hreg_of_exists_funCongrLeft` consumes.

The `eIn` certificate (`isCoordLE_eIn`) is DONE + axiom-clean. The only remaining piece is the parallel
`packStair` certificate `IsCoordLE (paramsEquivFlatLinear M) (stairChart M) (packStair ha)` (σ = the
`paramsEquivFlatLinear`-`FlatIdx` reindex composed with the `packLayer0`/`packLayer1` reshapes), an
`isCoordLE_of_read` whose read goes through `flatBlockLE.symm`/`rowSplitLE`/`prodComm`. Once banked, the
final assembly is `(isCoordLE_eIn ha).trans (isCoordLE_packStair ha |>.symm |> …)` fed through
`hreg_of_exists_funCongrLeft`. The single `sorry` below isolates that obligation. -/

/-- **`eihd_hreg` — the regauge abs-det is `1`** (the `hreg` slot of `interiorDet_leaf_headline_eihd`).
The composite `(eihdOut ha).symm ∘ₗ (eIn ha)` is a coordinate permutation `funCongrLeft σ` of the flat
space (every constituent of `eIn`/`eihdOut` is a `→ℝ` coordinate bijection), hence measure-preserving
with abs-det `1` (`hreg_of_exists_funCongrLeft`). The `eIn` half is `isCoordLE_eIn`; the `packStair`
half (the isolated `sorry`) is the parallel `IsCoordLE (paramsEquivFlatLinear) (stairChart) (packStair)`. -/
theorem eihd_hreg (ha : StructAdm M (tach M)) :
    |LinearMap.det (((eihdOut ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
        ∘ₗ ((eIn ha) : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2))| = 1 := by
  refine hreg_of_exists_funCongrLeft (eihdV M) (eIn ha) (eihdOut ha) ?_
  -- eIn half banked (isCoordLE_eIn); packStair half remaining (see docstring). Assemble via
  -- `IsCoordLE.trans` once `isCoordLE_packStair` is banked.
  sorry

end L2

end DLNFibre.DLN.RLCT

end
