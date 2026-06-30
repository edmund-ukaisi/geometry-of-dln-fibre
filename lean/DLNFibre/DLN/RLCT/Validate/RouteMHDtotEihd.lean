import DLNFibre.DLN.RLCT.Validate.RouteMHDtotConj
import DLNFibre.DLN.RLCT.Validate.RouteMFlatBlockLE
import DLNFibre.DLN.RLCT.Validate.RouteMRoleCLE

/-!
# `RouteMHDtotEihd` — the coupled `eIn`/`eihdOut`/`hD` two-sided staircase conjugacy of `Dtot` (∀M-L2)

The load-bearing geometric residual of `hDtot`. The assembly wrapper
`RouteMHDtotConj.hDtot_of_twoStairConj` reduces `hDtot : |det Dtot| = |det K|^(r+c)` to EXACTLY the
two layer-collecting equivs `eIn eihdOut : (Fin (flatDim M) → ℝ) ≃ₗ StairProd V 2`, the block identity
`hD : eihdOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c`, and `hreg` (discharged by the banked
`hreg_of_measurePreserving_comp`). This module BUILDS that trio as one coherent construction.

The numeric partition certificate (6 random seeds at (3,3,4), EXACT) fixes the design:
* `V 0 = SchurInc (Text2) (Text1−Text2) (Wext1−Text2)` — the boundary-0 Schur frame increment.
* `V 1 = Matrix(Wext1−Text2, Wext2) × Matrix(Text2, Wext2)` — the `(W, leaf)` chain layer.
* `f 0 = schurFrameDeriv X K N` (det `|det K|^(r+c)`), `f 1 = chainUnitMap (readN ⟨0⟩)` (det `1`).
* The shared `readN ⟨0⟩` couples the layer-0 frame (`K·N, X·K·N`) to the layer-1 kept row (`−N·W`) —
  strictly head→tail, the det-invisible coupling `c.1`.

The trio is COUPLED (a misaligned reindex is the green-but-wrong trap): the input role reindex,
the output Params-layer split, and the block identity must agree on the SAME `V 0`/`V 1` boundary
spaces. `eihdOut` absorbs the `paramsEquivFlat` flattening cleanly (`eihdOut := packStair ∘ₗ
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
`chainUnit_det` — independent of the geometric `eIn`/`eihdOut`/`hD`. -/

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

/-! ## The output `packStair : Params M ≃ₗ StairProd V 2` and `eihdOut`

`packStair` collects the two `Params` layers into the staircase product:
* layer 0 (`Matrix(M0,M1)`) → `V 0 = SchurInc` via the dim-recast `Matrix(M0,M1) ≃ Matrix(Text1,Wext1)`
  then `flatBlockLE.symm` (`M0 = Text1`, `M1 = Wext1`).
* layer 1 (`Matrix(M1,M2)`) → `V 1 = (W, leaf)` via the dim-recast `Matrix(M1,M2) ≃ Matrix(Wext1,Wext2)`
  then the ROW split `Fin Wext1 ≃ Fin Text2 ⊕ Fin (Wext1−Text2)` into `(kept, lift)`, REORDERED to
  `(lift = W, kept = leaf)` to match `chainUnitMap`'s `(W, C)` domain orientation (the flagged trap).

`eihdOut := packStair ∘ₗ paramsEquivFlatCLE.symm` absorbs the `paramsEquivFlat` flattening, so
`eihdOut ∘ paramsEquivFlatCLE = packStair` and `hD` reduces to `packStair ∘ (fderiv BparamsLeaf) ∘ eIn.symm
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

/-- **`eihdOut := packStair ∘ₗ paramsEquivFlatCLE.symm`** — the output layer-collecting equiv. Absorbs
the `paramsEquivFlat` flattening: `eihdOut ∘ paramsEquivFlatCLE = packStair` (so `hD` reduces to
`packStair ∘ (fderiv BparamsLeaf) ∘ eIn.symm = stairMap`). -/
noncomputable def eihdOut (ha : StructAdm M (tach M)) :
    (Fin (flatDim M) → ℝ) ≃ₗ[ℝ] StairProd (eihdV M) 2 :=
  (paramsEquivFlatLinear M).symm.trans (packStair ha)

/-! ## The input equiv `eIn` (RESIDUAL piece 1)

The slot-faithful input regroup. Its V0-component reads exactly the boundary-0 Schur frame slot —
`(eIn δ).1 = slotReadV0 ha δ` — so the J00 block computation is a clean read, not a reindex fight
(the Codex-endorsed Option B: `slotReadV0` is the V0 component DEFINITIONALLY). The V1-component reads
the boundary-0 lift slot (`W`) and the boundary-1 frame slot (`leaf`). -/

/-! ### The V0 frame-slot reshape `(Fin (schurDim 0) → ℝ) ≃ₗ SchurInc` (matching `frameSplitEquiv`)

The boundary-0 frame slot (`schurDim 0 = Text1·Wext1`) reshapes to the `SchurInc (t2, r1, c1)` tuple via
the SAME `frameSplitEquiv` the readers use: reindex `Fin (schurDim 0) → ℝ` by `frameSplitEquiv` to the
role-Sum-indexed Pi `(((K⊕X)⊕N)⊕E) → ℝ`, split off each role by `sumArrowLequivProdArrow`, reshape each
to its matrix, and REORDER `(K, X, N, E) → (K, N, X, E)` to match `slotReadV0`'s tuple. -/

/-- Reorder/reshape `(((K-coords × X-coords) × N-coords) × E-coords)` → `SchurInc (K, N, X, E)` —
the `frameSplitEquiv` role order is `(((K⊕X)⊕N)⊕E)` but `SchurInc`/`slotReadV0` is `(K, N, X, E)`. -/
noncomputable def roleReorderLE (M : Fin (2 + 1) → ℕ) :
    ((((Fin (schurT1 M * schurT1 M) → ℝ) × (Fin (schurR1 M * schurT1 M) → ℝ))
        × (Fin (schurT1 M * schurC1 M) → ℝ)) × (Fin (schurR1 M * schurC1 M) → ℝ))
      ≃ₗ[ℝ] SchurInc (schurT1 M) (schurR1 M) (schurC1 M) where
  toFun p :=
    (flatMatLE (schurT1 M) (schurT1 M) p.1.1.1,
     flatMatLE (schurT1 M) (schurC1 M) p.1.2,
     flatMatLE (schurR1 M) (schurT1 M) p.1.1.2,
     flatMatLE (schurR1 M) (schurC1 M) p.2)
  invFun z :=
    ((((flatMatLE (schurT1 M) (schurT1 M)).symm z.1,
       (flatMatLE (schurR1 M) (schurT1 M)).symm z.2.2.1),
      (flatMatLE (schurT1 M) (schurC1 M)).symm z.2.1),
     (flatMatLE (schurR1 M) (schurC1 M)).symm z.2.2.2)
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]; rfl
  map_smul' r a := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]; rfl
  left_inv p := by
    simp only [LinearEquiv.symm_apply_apply]
  right_inv z := by
    simp only [LinearEquiv.apply_symm_apply]

/-- The boundary-1 Schur role widths (`s = 1`, the V0 boundary): `frameSplitEquiv M t 1` splits
`Fin (Text1·Wext1)` into `K (t2·t2) ⊕ X (r1·t2) ⊕ N (t2·c1) ⊕ E (r1·c1)`. Reindex `Fin (schurDim 0) → ℝ`
by `frameSplitEquiv.symm`, peel the nested `⊕` from the outside (E, N, X, K), reshape + reorder. -/
noncomputable def frameToSchurInc (ha : StructAdm M (tach M)) :
    (Fin (schurDim M (tDesc M (tach M)) 0) → ℝ) ≃ₗ[ℝ]
      SchurInc (schurT1 M) (schurR1 M) (schurC1 M) :=
  (LinearEquiv.funCongrLeft ℝ ℝ
      (frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm).trans
    (((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans
        ((((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans
            (((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).prodCongr
              (LinearEquiv.refl ℝ _)))).prodCongr (LinearEquiv.refl ℝ _)))).trans
      (roleReorderLE M))

/-- The V1 leaf-slot reshape `(Fin (schurDim 1) → ℝ) ≃ₗ Matrix (schurT1) (Wext2)` — the boundary-1 frame
slot `schurDim 1 = Text2·Wext2` is the leaf residual matrix. -/
noncomputable def leafToMat (ha : StructAdm M (tach M)) :
    (Fin (schurDim M (tDesc M (tach M)) 1) → ℝ) ≃ₗ[ℝ]
      Matrix (Fin (schurT1 M)) (Fin (Wext M 2)) ℝ :=
  flatMatLE (schurT1 M) (Wext M 2)

/-- The product-indexed coords → matrix reshape `(Fin a × Fin b → ℝ) ≃ₗ Matrix (Fin a) (Fin b)`. -/
noncomputable def prodMatLE (a b : ℕ) :
    (Fin a × Fin b → ℝ) ≃ₗ[ℝ] Matrix (Fin a) (Fin b) ℝ :=
  (LinearEquiv.curry ℝ ℝ (Fin a) (Fin b)).trans (Matrix.ofLinearEquiv ℝ)

/-- The V1 W-slot reshape `(Fin (liftDim 0) → ℝ) ≃ₗ Matrix (schurC1) (Wext2)` — the boundary-0 lift slot
`liftDim 0 = (Wext1−Text2)·Wext2` is the lift `W` matrix. Reindex by `liftSlotEquiv.symm` to the
product-index `Fin schurC1 × Fin Wext2`, then `prodMatLE`. -/
noncomputable def wToMat (ha : StructAdm M (tach M)) :
    (Fin (liftDim M (tDesc M (tach M)) 0) → ℝ) ≃ₗ[ℝ]
      Matrix (Fin (schurC1 M)) (Fin (Wext M 2)) ℝ :=
  (LinearEquiv.funCongrLeft ℝ ℝ (liftSlotEquiv M (tDesc M (tach M)) 0 (by decide)).symm).trans
    (prodMatLE (schurC1 M) (Wext M 2))

/-- The empty lift slot `liftDim 1 = 0`, so `(Fin (liftDim 1) → ℝ) ≃ₗ PUnit` (the `Fin 0 → ℝ` zero
space). -/
theorem liftDim_one_eq_zero : liftDim M (tDesc M (tach M)) 1 = 0 := by
  rw [liftDim, if_neg (by decide)]

/-- The leaf lift slot is `PUnit`-like: `(Fin (liftDim 1) → ℝ) ≃ₗ PUnit` (both `Subsingleton`,
`liftDim 1 = 0`). -/
noncomputable def leafLiftToPUnit (ha : StructAdm M (tach M)) :
    (Fin (liftDim M (tDesc M (tach M)) 1) → ℝ) ≃ₗ[ℝ] PUnit := by
  haveI : Subsingleton (Fin (liftDim M (tDesc M (tach M)) 1) → ℝ) := by
    rw [liftDim_one_eq_zero]; infer_instance
  exact
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }

/-- The `eIn` final rearrange `((V0 × W) × (leaf × PUnit)) ≃ₗ V0 × ((W × leaf) × PUnit)` — collect the
two V1 matrix blocks `(W, leaf)` into `eihdV M 1` (the chain pair), keep `V0` head and the `PUnit` tail. -/
noncomputable def eInRearrange (ha : StructAdm M (tach M)) :
    (((eihdV M 0 × Matrix (Fin (schurC1 M)) (Fin (Wext M 2)) ℝ)
        × (Matrix (Fin (schurT1 M)) (Fin (Wext M 2)) ℝ × PUnit)))
      ≃ₗ[ℝ] StairProd (eihdV M) 2 where
  toFun p := (p.1.1, ((p.1.2, p.2.1), p.2.2))
  invFun q := ((q.1, q.2.1.1), (q.2.1.2, q.2.2))
  map_add' a b := rfl
  map_smul' r a := rfl
  left_inv p := rfl
  right_inv q := rfl

/-- The per-boundary slot split `(slot k → ℝ) ≃ₗ (Fin (schurDim k) → ℝ) × (Fin (liftDim k) → ℝ)`. -/
noncomputable def slotSplitLE (k : ℕ) :
    ((Fin (schurDim M (tDesc M (tach M)) k) ⊕ Fin (liftDim M (tDesc M (tach M)) k)) → ℝ)
      ≃ₗ[ℝ] (Fin (schurDim M (tDesc M (tach M)) k) → ℝ) × (Fin (liftDim M (tDesc M (tach M)) k) → ℝ) :=
  LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ

/-- **`eIn` (residual piece 1)** — the input layer-collecting equiv `(Fin (flatDim M) → ℝ) ≃ₗ
StairProd (eihdV M) 2`, V0-component `= slotReadV0`. Built (Option A) as a composite of `LinearEquiv`s
through `chartIdxEquiv`: `funCongrLeft chartIdxEquiv.symm` (flat → ChartIdx-Pi), `piCurry` (Σ → nested
Π), `piFinTwo` (Π over `Fin 2` → product), per-boundary `slotSplitLE` (frame/lift split), then reshape
each slot to `V0`/`V1` and rearrange `(V0 × W) × (leaf × PUnit) → V0 × ((W, leaf) × PUnit)`. -/
noncomputable def eIn (ha : StructAdm M (tach M)) :
    (Fin (flatDim M) → ℝ) ≃ₗ[ℝ] StairProd (eihdV M) 2 :=
  -- step 1: flat → ChartIdx-indexed Pi
  LinearEquiv.funCongrLeft ℝ ℝ
      (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ≪≫ₗ
  -- step 2: Σ → nested Π (piCurry, constant codomain ℝ)
  LinearEquiv.piCurry ℝ (κ := fun k : Fin 2 =>
      Fin (schurDim M (tDesc M (tach M)) k.val) ⊕ Fin (liftDim M (tDesc M (tach M)) k.val))
      (fun _ _ => ℝ) ≪≫ₗ
  -- step 3: Π over `Fin 2` → product (slot 0 × slot 1)
  LinearEquiv.piFinTwo ℝ (fun k : Fin 2 =>
      (Fin (schurDim M (tDesc M (tach M)) k.val) ⊕ Fin (liftDim M (tDesc M (tach M)) k.val)) → ℝ) ≪≫ₗ
  -- step 4: split each slot, reshape, rearrange
  ((slotSplitLE 0).prodCongr (slotSplitLE 1)) ≪≫ₗ
  (((frameToSchurInc ha).prodCongr (wToMat ha)).prodCongr
      ((leafToMat ha).prodCongr (leafLiftToPUnit ha))) ≪≫ₗ
  eInRearrange ha

/-- `flatMatLE a b f i j = f (finProdFinEquiv (i, j))` — the flat-slot ↔ matrix reshape reads the slot
coord at the `finProdFinEquiv`-packed index (the `funCongrLeft ≫ curry ≫ ofLinearEquiv` eval). -/
theorem flatMatLE_apply (a b : ℕ) (f : Fin (a * b) → ℝ) (i : Fin a) (j : Fin b) :
    flatMatLE a b f i j = f (finProdFinEquiv (i, j)) := by
  unfold flatMatLE; simp only [LinearEquiv.trans_apply]; rfl

/-- The four `SchurInc` blocks of `frameToSchurInc ha g` read `g` at the `frameSplitEquiv.symm` role
indices — exactly the indices `readK/N/X/E … ⟨0⟩` use, after the `roleReorderLE` `(K,X,N,E) → (K,N,X,E)`
reshuffle: K@`inl inl inl`, N@`inl inr`, X@`inl inl inr`, E@`inr`. -/
theorem frameToSchurInc_blocks (ha : StructAdm M (tach M))
    (g : Fin (schurDim M (tDesc M (tach M)) 0) → ℝ) :
    frameToSchurInc ha g
      = (Matrix.of (fun i j =>
          g ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
            (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, j))))))),
         Matrix.of (fun i j =>
          g ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
            (Sum.inl (Sum.inr (finProdFinEquiv (i, j)))))),
         Matrix.of (fun i j =>
          g ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
            (Sum.inl (Sum.inl (Sum.inr (finProdFinEquiv (i, j))))))),
         Matrix.of (fun i j =>
          g ((frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm
            (Sum.inr (finProdFinEquiv (i, j)))))) := by
  -- peel the outer `roleReorderLE` (`rfl`); each block is `flatMatLE` of a `sumArrow`-split coord
  have hr : frameToSchurInc ha g
      = roleReorderLE M
          ((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ ≪≫ₗ
            (((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans
                (((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).prodCongr
                  (LinearEquiv.refl ℝ _)))).prodCongr (LinearEquiv.refl ℝ _)))
            ((LinearEquiv.funCongrLeft ℝ ℝ
                (frameSplitEquiv M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0)).symm) g)) := rfl
  rw [hr]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> ext i j
  · show flatMatLE (schurT1 M) (schurT1 M) _ i j = _
    rw [flatMatLE_apply]
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.sumArrowLequivProdArrow_apply_fst, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, Matrix.of_apply]
  · show flatMatLE (schurT1 M) (schurC1 M) _ i j = _
    rw [flatMatLE_apply]
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.sumArrowLequivProdArrow_apply_fst, LinearEquiv.sumArrowLequivProdArrow_apply_snd,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Matrix.of_apply]
  · show flatMatLE (schurR1 M) (schurT1 M) _ i j = _
    rw [flatMatLE_apply]
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.sumArrowLequivProdArrow_apply_fst, LinearEquiv.sumArrowLequivProdArrow_apply_snd,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Matrix.of_apply]
  · show flatMatLE (schurR1 M) (schurC1 M) _ i j = _
    rw [flatMatLE_apply]
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.sumArrowLequivProdArrow_apply_snd, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, Matrix.of_apply]

/-- **The V0-faithfulness invariant**: `(eIn ha δ).1 = slotReadV0 ha δ` — the boundary-0 frame slot.
The in-Lean check that `eIn` reads the Schur frame into V0; with `hD`'s J00 match this catches a
misaligned reindex. `(eIn δ).1 = frameToSchurInc ha g` (`rfl`) with `g a = δ (chartIdxEquiv.symm
⟨0, Sum.inl a⟩)`; `frameToSchurInc_blocks` reads the 4 `SchurInc` blocks (K, N, X, E) at exactly the
`readK/N/X/E … ⟨0⟩` slot indices, so the `(readK, readN, readX, readE) = slotReadV0` match is `rfl`. -/
theorem eIn_projV0 (ha : StructAdm M (tach M)) (δ : Fin (flatDim M) → ℝ) :
    (eIn ha δ).1 = slotReadV0 ha δ := by
  -- `(eIn δ).1 = frameToSchurInc ha g` (rfl) with `g a = δ (chartIdxEquiv.symm ⟨0, Sum.inl a⟩)`
  have hg : (eIn ha δ).1 = frameToSchurInc ha
      (fun a => δ ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨0, Sum.inl a⟩)) := rfl
  rw [hg, frameToSchurInc_blocks ha]
  -- both sides are the 4-tuple of readers; `slotReadV0 = (readK, readN, readX, readE)` matches
  rfl

/-! ## The block identity `hD` (RESIDUAL piece 2)

`hD : eihdOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c` at the pivot-blowup point. With the coupling `c`
DEFINED from the actual off-diagonal block of `T := eihdOut ∘ Dtot ∘ eIn.symm` (Codex's "even better":
`c.1 v0 := (projV1 (T (inclV0 v0)), ())`), `hD` reduces to the THREE diagonal/off-diagonal block facts:
`projV0 ∘ T ∘ inclV0 = f 0` (J00, the Schur frame — the faithfulness gate for `eIn`),
`projV0 ∘ T ∘ inclV1 = 0` (J01, the det-invisible upper block),
`projV1 ∘ T ∘ inclV1 = f 1` (J11, the chain unit). -/

/-- The flat-Jacobian conjugate `T := eihdOut ∘ Dtot ∘ eIn.symm` at the pivot-blowup point — the
endomorphism of `StairProd (eihdV M) 2` whose staircase the block facts read. -/
noncomputable def eihdT (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ) :
    StairProd (eihdV M) 2 →ₗ[ℝ] StairProd (eihdV M) 2 :=
  (eihdOut ha : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2)
    ∘ₗ Dtot ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u)
    ∘ₗ ((eIn ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))

/-- The V0-inclusion `inclV0 : V 0 →ₗ StairProd V 2`, `v0 ↦ (v0, (0, ()))` — `LinearMap.inl` into the
head, the tail at `0`. The head-into-tail coupling reads `T` along this inclusion. -/
noncomputable def eihdInclV0 :
    eihdV M 0 →ₗ[ℝ] StairProd (eihdV M) 2 :=
  LinearMap.inl ℝ (eihdV M 0) (StairProd (fun k => eihdV M (k + 1)) 1)

@[simp] theorem eihdInclV0_apply (v0 : eihdV M 0) :
    eihdInclV0 (M := M) v0 = (v0, (0 : StairProd (fun k => eihdV M (k + 1)) 1)) := rfl

/-- **The staircase coupling `c`**, DEFINED from the actual off-diagonal block of `T` (Codex's "even
better": the V0→V1 head-into-tail coupling is whatever `T` does, never separately identified — it is
det-invisible). `c.1 = projTail ∘ T ∘ inclV0` (a `LinearMap` composite, so linearity is automatic);
`c.2 = (0, ())` (the leaf has no lower layer). -/
noncomputable def eihdc (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ) :
    StairCoupling (eihdV M) 2 :=
  ⟨(LinearMap.snd ℝ (eihdV M 0) (StairProd (fun k => eihdV M (k + 1)) 1)).comp
      ((eihdT ha h0r h0c u).comp (eihdInclV0 (M := M))),
    ⟨0, PUnit.unit⟩⟩

/-- `eihdc.1 v0 = (eihdT … (v0, (0, ()))).2` — the coupling reads the tail of `T` along `inclV0`. -/
theorem eihdc_fst_apply (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ) (v0 : eihdV M 0) :
    (eihdc ha h0r h0c u).1 v0 = (eihdT ha h0r h0c u (v0, (0, PUnit.unit))).2 := rfl

/-- **Bridge 1 — the flatten/unflatten cancel**: `eihdT w = packStair (fderiv BparamsLeaf y₀ (eIn.symm
w))`. `eihdOut = paramsEquivFlatLinear.symm ≫ packStair` and `Dtot = paramsEquivFlatCLE ∘ fderiv
BparamsLeaf`, so the `paramsEquivFlatLinear.symm ∘ paramsEquivFlatCLE` round-trip is the identity (same
underlying map), leaving `packStair ∘ (fderiv BparamsLeaf) ∘ eIn.symm`. Reduces all three J-blocks to
facts about the `Params`-valued `fderiv BparamsLeaf` applied at `eIn.symm w`, then `packStair`-projected. -/
theorem eihdT_eq_packStair_fderiv (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ) (w : StairProd (eihdV M) 2) :
    eihdT ha h0r h0c u w
      = packStair ha (fderiv ℝ (fun z => BparamsLeaf ha z)
          (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u)
          ((eIn ha).symm w)) := by
  show (eihdOut ha) ((Dtot ha _) ((eIn ha).symm w)) = _
  unfold eihdOut Dtot
  rw [LinearEquiv.trans_apply]
  congr 1
  show (paramsEquivFlatLinear M).symm
      ((paramsEquivFlatCLE M) (fderiv ℝ (fun z => BparamsLeaf ha z) _ ((eIn ha).symm w))) = _
  rw [show ⇑(paramsEquivFlatCLE M) = ⇑(paramsEquivFlatLinear M) from by
        rw [paramsEquivFlatCLE_coe, paramsEquivFlatLinear_coe]]
  exact (paramsEquivFlatLinear M).symm_apply_apply _

/-- **J00 — the Schur-frame block** (part of the in-Lean faithfulness gate for `eIn`, with J01/J11).
The V0→V0 block of `T` is `eihdF … 0 = schurFrameDeriv X K N`. -/
theorem eihdT_J00 (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ)
    (v0 : eihdV M 0) :
    (eihdT ha h0r h0c u (v0, (0, PUnit.unit))).1
      = eihdF ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u) 0 v0 :=
  sorry

/-- **J01 = 0 — the upper block** (part of the in-Lean faithfulness gate for `eIn`, with J00/J11). The
V1→V0 block of `T` is `0`: the layer-1 (chain) coordinates do not feed the layer-0 (frame) Schur output. -/
theorem eihdT_J01 (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ)
    (v1 : eihdV M 1) :
    (eihdT ha h0r h0c u (0, (v1, PUnit.unit))).1 = 0 :=
  sorry

/-- **J11 — the chain-unit block** (part of the in-Lean faithfulness gate for `eIn`, with J00/J01 — the
V1-line of `eihd_hD` cannot close without it). The V1→V1 block of `T` is
`eihdF … 1 = chainUnitMap (readN ⟨0⟩)`: the layer-1 chaining `(W, C) ↦ (W, C − N·W)`. -/
theorem eihdT_J11 (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ)
    (v1 : eihdV M 1) :
    (eihdT ha h0r h0c u (0, (v1, PUnit.unit))).2.1
      = (eihdF ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u) 1 v1) :=
  sorry

/-- **`hD` — the block identity** `eihdOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c`, assembled from the
three block facts (J00/J01/J11) with `c` the off-diagonal coupling. `LinearMap.ext` over arbitrary
`(v0, (v1, ()))`; the V0-component is `f0 v0 + 0` (J00 + J01), the V1-component is `f1 v1 + (coupling)`
(J11 + the defined `c.1`). -/
theorem eihd_hD (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    (eihdOut ha : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2)
        ∘ₗ Dtot ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u)
        ∘ₗ ((eIn ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
      = stairMap (eihdV M) 2
          (eihdF ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u))
          (eihdc ha h0r h0c u) := by
  -- the LHS is `eihdT`; ext over `StairProd (eihdV M) 2 = V0 × (V1 × PUnit)`
  apply LinearMap.ext
  rintro ⟨v0, v1, ⟨⟩⟩
  -- the LHS composite applied at the point IS `eihdT … (v0,(v1,()))`; rewrite to that, then split.
  have hT : ((eihdOut ha : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2)
        ∘ₗ Dtot ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u)
        ∘ₗ ((eIn ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ)))
          (v0, (v1, PUnit.unit))
      = eihdT ha h0r h0c u (v0, (v1, PUnit.unit)) := rfl
  rw [hT]
  -- `eihdT` is linear: split `(v0,(v1,())) = inclV0 v0 + inclV1 v1`
  have hsplit : ((v0, (v1, PUnit.unit)) : StairProd (eihdV M) 2)
      = (v0, ((0 : eihdV M 1), PUnit.unit)) + (0, (v1, PUnit.unit)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show v0 = v0 + 0; exact (add_zero v0).symm
    · show v1 = 0 + v1; exact (zero_add v1).symm
    · rfl
  have happ : eihdT ha h0r h0c u (v0, (v1, PUnit.unit))
      = eihdT ha h0r h0c u (v0, ((0 : eihdV M 1), PUnit.unit))
        + eihdT ha h0r h0c u (0, (v1, PUnit.unit)) := by
    rw [hsplit]; exact map_add _ _ _
  rw [happ]
  -- the `stairMap` RHS at the point reduces (def of `stairMap`/`lowerTri`) to
  -- `(f0 v0, (f1 v1 + (c.1 v0).1, (c.1 v0).2))`
  set f := eihdF ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u) with hf
  set c := eihdc ha h0r h0c u with hc
  show eihdT ha h0r h0c u (v0, (0, PUnit.unit)) + eihdT ha h0r h0c u (0, (v1, PUnit.unit))
      = (f 0 v0, ((f 1 v1 + (c.1 v0).1), (c.1 v0).2))
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- V0: (J00 v0) + (J01 v1) = f0 v0 + 0 = f0 v0
    show (eihdT ha h0r h0c u (v0, (0, PUnit.unit))).1
        + (eihdT ha h0r h0c u (0, (v1, PUnit.unit))).1 = f 0 v0
    rw [eihdT_J00 ha h0r h0c u v0, eihdT_J01 ha h0r h0c u v1, add_zero]
  · -- V1: (J·0 V1-feed) + (J11 v1) = f1 v1 + (c.1 v0).1; by `eihdc`, `(c.1 v0).1 = (J·0 feed)`
    show (eihdT ha h0r h0c u (v0, (0, PUnit.unit))).2.1
        + (eihdT ha h0r h0c u (0, (v1, PUnit.unit))).2.1 = f 1 v1 + (c.1 v0).1
    rw [eihdT_J11 ha h0r h0c u v1, add_comm]
    rfl
  · -- PUnit component (`StairProd V 0 = PUnit`)
    rfl

end L2

/-! ## The assembly: `hDtot`/headline from the residual `(eIn, c, hD, hreg)`

Everything except the regauge `hreg` is now BANKED or BUILT: the boundary spaces `eihdV`, the diagonal
blocks `eihdF` (with both dets), the output equiv `eihdOut`, the input equiv `eIn`, the coupling `eihdc`,
and the block identity `eihd_hD`. This theorem feeds them through `hDtot_of_twoStairConj` +
`interiorDet_leaf_headline_freeK`. -/

section L2

variable {M : Fin (2 + 1) → ℕ}

/-- **The ∀M-L2 interior-det headline from the residual** — the wrapper
`interiorDet_leaf_headline_of_DtotConj` instantiated with the banked/built `eihdV`/`eihdF`/`eihdOut`/
`eIn`/`eihdc`/`eihd_hD` and the two banked block dets (`eihdF0_abs_det`/`eihdF1_abs_det`). The only
remaining hypothesis is the regauge abs-det-`1` `hreg`. -/
theorem interiorDet_leaf_headline_eihd (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ)
    (hreg : |LinearMap.det (((eihdOut ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
        ∘ₗ ((eIn ha) : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2))| = 1) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveAt M ha (by norm_num)
        (leafPivot M ha (by norm_num) h0r h0c)) u).toLinearMap|
      = |u (leafPivot M ha (by norm_num) h0r h0c)| ^ (minAdm M - 1)
        * ∏ s : Fin 2, engineFreeK ha h0r h0c u s :=
  interiorDet_leaf_headline_of_DtotConj (eihdV M) ha h0r h0c u
    (eihdF ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u))
    (eihdc ha h0r h0c u)
    (eIn ha) (eihdOut ha) (eihd_hD ha h0r h0c u) hreg
    (eihdF0_abs_det ha h0r h0c u) (eihdF1_abs_det ha _)

end L2

end DLNFibre.DLN.RLCT

end
