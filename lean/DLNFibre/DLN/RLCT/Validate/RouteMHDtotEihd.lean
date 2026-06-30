import DLNFibre.DLN.RLCT.Validate.RouteMHDtotConj
import DLNFibre.DLN.RLCT.Validate.RouteMFlatBlockLE
import DLNFibre.DLN.RLCT.Validate.RouteMRoleCLE

/-!
# `RouteMHDtotEihd` — the coupled `eIn`/`eOut`/`hD` two-sided staircase conjugacy of `Dtot` (∀M-L2)

The load-bearing geometric residual of `hDtot`. The assembly wrapper
`RouteMHDtotConj.hDtot_of_twoStairConj` reduces `hDtot : |det Dtot| = |det K|^(r+c)` to EXACTLY the
two layer-collecting equivs `eIn eOut : (Fin (flatDim M) → ℝ) ≃ₗ StairProd V 2`, the block identity
`hD : eOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c`, and `hreg` (discharged by the banked
`hreg_of_measurePreserving_comp`). This module BUILDS that trio as one coherent construction.

The numeric partition certificate (6 random seeds at (3,3,4), EXACT) fixes the design:
* `V 0 = SchurInc (Text2) (Text1−Text2) (Wext1−Text2)` — the boundary-0 Schur frame increment.
* `V 1 = Matrix(Wext1−Text2, Wext2) × Matrix(Text2, Wext2)` — the `(W, leaf)` chain layer.
* `f 0 = schurFrameDeriv X K N` (det `|det K|^(r+c)`), `f 1 = chainUnitMap (readN ⟨0⟩)` (det `1`).
* The shared `readN ⟨0⟩` couples the layer-0 frame (`K·N, X·K·N`) to the layer-1 kept row (`−N·W`) —
  strictly head→tail, the det-invisible coupling `c.1`.

The trio is COUPLED (a misaligned reindex is the green-but-wrong trap): the input role reindex,
the output Params-layer split, and the block identity must agree on the SAME `V 0`/`V 1` boundary
spaces. `eOut` absorbs the `paramsEquivFlat` flattening cleanly (`eOut := packStair ∘ₗ
paramsEquivFlatCLE.symm`), so `hD` reduces to `packStair ∘ (fderiv BparamsLeaf) ∘ eIn.symm =
stairMap`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` target.
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

section L2

variable {M : Fin (2 + 1) → ℕ}

/-! ## The boundary spaces `V` of the two-sided staircase (`StairProd V 2`) -/

/-- The staircase boundary spaces for the `Dtot` conjugacy at `L = 2`:
`V 0 = SchurInc` (the Schur frame increment), `V 1 = (W, leaf)` chain pair, `V s = PUnit` else. -/
def eihdV (M : Fin (2 + 1) → ℕ) : ℕ → Type
  | 0 => SchurInc (schurT1 M) (schurR1 M) (schurC1 M)
  | 1 => Matrix (Fin (schurC1 M)) (Fin (Wext M 2)) ℝ × Matrix (Fin (schurT1 M)) (Fin (Wext M 2)) ℝ
  | (_ + 2) => PUnit

instance eihdV_addCommGroup (M : Fin (2 + 1) → ℕ) : ∀ k, AddCommGroup (eihdV M k)
  | 0 => (inferInstance : AddCommGroup (SchurInc _ _ _))
  | 1 => (inferInstance : AddCommGroup (Matrix _ _ ℝ × Matrix _ _ ℝ))
  | (_ + 2) => (inferInstance : AddCommGroup PUnit)

instance eihdV_module (M : Fin (2 + 1) → ℕ) : ∀ k, Module ℝ (eihdV M k)
  | 0 => (inferInstance : Module ℝ (SchurInc _ _ _))
  | 1 => (inferInstance : Module ℝ (Matrix _ _ ℝ × Matrix _ _ ℝ))
  | (_ + 2) => (inferInstance : Module ℝ PUnit)

instance eihdV_finite (M : Fin (2 + 1) → ℕ) : ∀ k, FiniteDimensional ℝ (eihdV M k)
  | 0 => (inferInstance : FiniteDimensional ℝ (SchurInc _ _ _))
  | 1 => (inferInstance : FiniteDimensional ℝ (Matrix _ _ ℝ × Matrix _ _ ℝ))
  | (_ + 2) => (inferInstance : FiniteDimensional ℝ PUnit)

/-! ## The diagonal blocks `f` and the coupling `c` -/

/-- The diagonal blocks: `f 0 = schurFrameDeriv X K N` (read at `slotReadV0 ha y₀`),
`f 1 = chainUnitMap (readN ⟨0⟩)`, `f s = 0` else. The det inputs are read at the pivot-blowup point. -/
def eihdF (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    (s : ℕ) → eihdV M s →ₗ[ℝ] eihdV M s
  | 0 => schurFrameDeriv (readX M (tach M) ha y₀ ⟨0, by decide⟩)
      (readK M (tach M) ha y₀ ⟨0, by decide⟩) (readN M (tach M) ha y₀ ⟨0, by decide⟩)
  | 1 => chainUnitMap (m' := Wext M 2) (readN M (tach M) ha y₀ ⟨0, by decide⟩)
  | (_ + 2) => 0

/-! ## The two diagonal-block determinants `hf0`/`hf1` (banked, no analysis)

The boundary-`0` block det is the banked Schur value, the leaf block det is `1`. These discharge the
two `hf*` hypotheses of `hDtot_of_twoStairConj` directly from the banked `schurFrameDeriv_det` /
`chainUnit_det` — independent of the geometric `eIn`/`eOut`/`hD`. -/

/-- `|det (eihdF … 0)| = |det K|^(r+c)` — the boundary-`0` Schur block, via `schurFrameDeriv_det`,
with `K = readK ⟨0⟩ = (slotReadV0 ha y₀).1 = leafKcore`. The `r+c` exponent matches the headline. -/
theorem eihdF0_abs_det (ha : StructAdm M (tach M)) (h0r : 0 < Text M (tach M) 2)
    (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (eihdF ha (pivotBlowupOn (activeM M ha)
        (leafPivot M ha (by norm_num) h0r h0c) u) 0)|
      = |(leafKcore ha h0r h0c u).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)) := by
  change |LinearMap.det (schurFrameDeriv _ _ _)| = _
  rw [schurFrame_abs_det]
  rfl

/-- `|det (eihdF … 1)| = 1` — the leaf chain block, via `chainUnit_det`. -/
theorem eihdF1_abs_det (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (eihdF ha y₀ 1)| = 1 := by
  change |LinearMap.det (chainUnitMap (m' := Wext M 2) _)| = 1
  rw [chainUnit_det, abs_one]

end L2

/-! ## Reshape `LinearEquiv` building blocks (pure linear algebra; no analysis)

`flatMatLE a b : (Fin (a*b) → ℝ) ≃ₗ Matrix (Fin a) (Fin b) ℝ` — flat coords of a product slot to the
matrix, via `funCongrLeft finProdFinEquiv` (`(Fin (a*b) → ℝ) ≃ (Fin a × Fin b → ℝ)`),
`LinearEquiv.curry` (`(Fin a × Fin b → ℝ) ≃ (Fin a → Fin b → ℝ)`), `Matrix.ofLinearEquiv`. -/

/-- `(Fin (a*b) → ℝ) ≃ₗ Matrix (Fin a) (Fin b) ℝ` — the flat-slot ↔ matrix reshape. -/
noncomputable def flatMatLE (a b : ℕ) :
    (Fin (a * b) → ℝ) ≃ₗ[ℝ] Matrix (Fin a) (Fin b) ℝ :=
  (LinearEquiv.funCongrLeft ℝ ℝ finProdFinEquiv).trans
    ((LinearEquiv.curry ℝ ℝ (Fin a) (Fin b)).trans (Matrix.ofLinearEquiv ℝ))

section L2

variable {M : Fin (2 + 1) → ℕ}

/-! ## The `flatBlock` fderiv normalization (`fderiv flatBlock = flatBlockLin`) — the J00 de-risk

The gate's V0-output reshape `flatBlock` is LINEAR (`flatBlockLin`), so its fderiv at any point IS
`flatBlockLin` (constant). Composing `flatBlockLE.symm` then recovers the identity on `SchurInc` —
the normalization that collapses the gate's `flatBlockD ∘ schurFrameD ∘ slotReadV0D` to
`schurFrameDeriv ∘ slotReadV0D` (the J00 Schur core). -/

/-- `fderiv (flatBlock hr hc) z₀ = flatBlockLin hr hc` (the flatten is linear). -/
theorem fderiv_flatBlock_eq {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol)
    (z₀ : SchurInc t r c) :
    (fderiv ℝ (fun z => flatBlock hr hc z) z₀).toLinearMap = flatBlockLin hr hc := by
  have hlin : HasFDerivAt (fun z => flatBlock hr hc z)
      (LinearMap.toContinuousLinearMap (flatBlockLin hr hc)) z₀ :=
    (LinearMap.toContinuousLinearMap (flatBlockLin hr hc)).hasFDerivAt
  rw [hlin.fderiv]
  rfl

/-- **The J00 normalization**: `flatBlockLE.symm ∘ (fderiv flatBlock z₀) = id` on `SchurInc` — the
output reshape `flatBlockLE.symm` cancels the linear flatten. The de-risk that collapses the gate's
`flatBlockD` factor, leaving `schurFrameDeriv` as the V0→V0 block. -/
theorem flatBlockLE_symm_fderiv_flatBlock {t r c Trow Wcol : ℕ}
    (hr : t + r = Trow) (hc : t + c = Wcol) (z₀ : SchurInc t r c) :
    ((flatBlockLE hr hc).symm : Matrix (Fin Trow) (Fin Wcol) ℝ →ₗ[ℝ] SchurInc t r c)
        ∘ₗ (fderiv ℝ (fun z => flatBlock hr hc z) z₀).toLinearMap
      = LinearMap.id := by
  rw [fderiv_flatBlock_eq hr hc z₀]
  apply LinearMap.ext
  intro z
  show (flatBlockLE hr hc).symm (flatBlockLin hr hc z) = z
  exact unflatBlock_flatBlock hr hc z

/-! ## The output `packStair : Params M ≃ₗ StairProd V 2` and `eOut`

`packStair` collects the two `Params` layers into the staircase product:
* layer 0 (`Matrix(M0,M1)`) → `V 0 = SchurInc` via the dim-recast `Matrix(M0,M1) ≃ Matrix(Text1,Wext1)`
  then `flatBlockLE.symm` (`M0 = Text1`, `M1 = Wext1`).
* layer 1 (`Matrix(M1,M2)`) → `V 1 = (W, leaf)` via the dim-recast `Matrix(M1,M2) ≃ Matrix(Wext1,Wext2)`
  then the ROW split `Fin Wext1 ≃ Fin Text2 ⊕ Fin (Wext1−Text2)` into `(kept, lift)`, REORDERED to
  `(lift = W, kept = leaf)` to match `chainUnitMap`'s `(W, C)` domain orientation (the flagged trap).

`eOut := packStair ∘ₗ paramsEquivFlatCLE.symm` absorbs the `paramsEquivFlat` flattening, so
`eOut ∘ paramsEquivFlatCLE = packStair` and `hD` reduces to `packStair ∘ (fderiv BparamsLeaf) ∘ eIn.symm
= stairMap`. -/

/-- The boundary width facts at `L = 2`: `M 0 = Text 1`, `M 1 = Wext 1`, `M 2 = Wext 2`. -/
theorem eihd_M0_eq_Text1 (ha : StructAdm M (tach M)) : M 0 = Text M (tach M) 1 := by
  have h := Text0_eq_Text1_struct M (tach M) ha.h0; rw [Text_zero] at h; exact h

theorem eihd_M1_eq_Wext1 : M 1 = Wext M 1 := by
  rw [Wext_apply M 1 (by omega)]; congr 1

theorem eihd_M2_eq_Wext2 : M 2 = Wext M 2 := by
  rw [Wext_apply M 2 (by omega)]; congr 1

/-- The row/col split facts: `schurT1 + schurR1 = Text 1`, `schurT1 + schurC1 = Wext 1`,
`schurT1 + schurC1 = Wext 1` (the V1 row split is `Text2 + (Wext1−Text2) = Wext1`). -/
theorem eihd_schurR_split (ha : StructAdm M (tach M)) :
    schurT1 M + schurR1 M = Text M (tach M) 1 := by
  have h : Text M (tach M) 2 ≤ Text M (tach M) 1 := ha.hdesc 0 (by decide)
  simp only [schurT1, schurR1]; omega

theorem eihd_schurC_split (ha : StructAdm M (tach M)) :
    schurT1 M + schurC1 M = Wext M 1 := by
  have h : Text M (tach M) 2 ≤ Wext M 1 := ha.hub 0
  simp only [schurT1, schurC1]; omega

/-! ### The two layer reshapes (the components of `packStair`) -/

/-- The layer-0 reshape `Matrix (M 0) (M 1) ≃ₗ V 0 = SchurInc` — dim-recast `Matrix(M0,M1) ≃
Matrix(Text1,Wext1)` then `flatBlockLE.symm`. (`M0 = Text1`, `M1 = Wext1`.) -/
noncomputable def packLayer0 (ha : StructAdm M (tach M)) :
    Matrix (Fin (M 0)) (Fin (M 1)) ℝ ≃ₗ[ℝ] eihdV M 0 :=
  (Matrix.reindexLinearEquiv ℝ ℝ (finCongr (eihd_M0_eq_Text1 ha)) (finCongr eihd_M1_eq_Wext1)).trans
    (flatBlockLE (eihd_schurR_split ha) (eihd_schurC_split ha)).symm

/-- The row-split of a `Matrix(Wext1, Wext2)` into `(kept = Matrix(schurT1,Wext2)) ×
(lift = Matrix(schurC1,Wext2))` — reindex rows by `(finSumFinEquiv).symm` to `Fin schurT1 ⊕ Fin schurC1`,
then `sumArrowLequivProdArrow`, then `ofLinearEquiv` on each component. (`schurT1 + schurC1 = Wext1`.) -/
noncomputable def rowSplitLE (ha : StructAdm M (tach M)) :
    Matrix (Fin (Wext M 1)) (Fin (Wext M 2)) ℝ ≃ₗ[ℝ]
      Matrix (Fin (schurT1 M)) (Fin (Wext M 2)) ℝ × Matrix (Fin (schurC1 M)) (Fin (Wext M 2)) ℝ :=
  (Matrix.reindexLinearEquiv ℝ ℝ
      (finSumFinEquiv.trans (finCongr (eihd_schurC_split ha))).symm
      (Equiv.refl (Fin (Wext M 2)))).trans
    (((Matrix.ofLinearEquiv ℝ).symm.trans
        (LinearEquiv.sumArrowLequivProdArrow (Fin (schurT1 M)) (Fin (schurC1 M)) ℝ
          (Fin (Wext M 2) → ℝ))).trans
      ((Matrix.ofLinearEquiv ℝ).prodCongr (Matrix.ofLinearEquiv ℝ)))

/-- The layer-1 reshape `Matrix (M 1) (M 2) ≃ₗ V 1 = (W, leaf)` — dim-recast `Matrix(M1,M2) ≃
Matrix(Wext1,Wext2)`, ROW-split into `(kept = leaf) × (lift = W)`, then SWAP to `(W, leaf)` — the
`chainUnitMap (W, C)` orientation (the flagged trap). -/
noncomputable def packLayer1 (ha : StructAdm M (tach M)) :
    Matrix (Fin (M 1)) (Fin (M 2)) ℝ ≃ₗ[ℝ] eihdV M 1 :=
  (Matrix.reindexLinearEquiv ℝ ℝ (finCongr eihd_M1_eq_Wext1) (finCongr eihd_M2_eq_Wext2)).trans
    ((rowSplitLE ha).trans (LinearEquiv.prodComm ℝ _ _))

/-- **`packStair : Params M ≃ₗ StairProd (eihdV M) 2`** — the output collector. Split the `Fin 2` Pi
into the two layers (`piFinTwo`), reshape each (`packLayer0`/`packLayer1`), then append the `PUnit`
tail (`prodUnique.symm`) to land in `V 0 × (V 1 × PUnit)`. -/
noncomputable def packStair (ha : StructAdm M (tach M)) :
    Params M ≃ₗ[ℝ] StairProd (eihdV M) 2 :=
  (LinearEquiv.piFinTwo ℝ (fun s : Fin 2 => Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ)).trans
    (((packLayer0 ha).prodCongr (packLayer1 ha)).trans
      ((LinearEquiv.refl ℝ (eihdV M 0)).prodCongr
        (LinearEquiv.prodUnique (R := ℝ) (M := eihdV M 1) (M₂ := PUnit)).symm))

/-- **`eOut := packStair ∘ₗ paramsEquivFlatCLE.symm`** — the output layer-collecting equiv. Absorbs
the `paramsEquivFlat` flattening: `eOut ∘ paramsEquivFlatCLE = packStair` (so `hD` reduces to
`packStair ∘ (fderiv BparamsLeaf) ∘ eIn.symm = stairMap`). -/
noncomputable def eOut (ha : StructAdm M (tach M)) :
    (Fin (flatDim M) → ℝ) ≃ₗ[ℝ] StairProd (eihdV M) 2 :=
  (paramsEquivFlatLinear M).symm.trans (packStair ha)

end L2

end DLNFibre.DLN.RLCT

end
