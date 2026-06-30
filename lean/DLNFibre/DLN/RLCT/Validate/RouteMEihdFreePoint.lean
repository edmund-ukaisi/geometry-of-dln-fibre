import DLNFibre.DLN.RLCT.Validate.RouteMHDtotEihd

/-!
# `RouteMEihdFreePoint` — the FREE-`y₀` `Dtot` two-sided staircase det (`Dtot_abs_det_free`)

The point-fixed `RouteMHDtotConj.hDtot_of_twoStairConj` proves `|det (Dtot ha (pbo u))| = |det K|^(r+c)`
with `K = leafKcore = readK ⟨0⟩` read at the pivot-blowup point `pbo u`. genm-ambdet (the ambient det
+ chain-rule fold hand) needs the SAME identity at a FREE evaluation point `y₀` (it instantiates at
`y₀ = Z = kLDU (pbo u)`), as factor 1 of the `BdetMonomial` chain-rule.

This module GENERALIZES the `pbo u`-fixed eihd staircase to a free `y₀`. The route (ROUTE 1, the cheap
path): the eihd machinery in `RouteMHDtotEihd` is point-FIXED to `pbo u` only via the closing
`set y₀ := pbo u` — its atoms are y₀-parametric (`eihdF` already takes `y₀`; `eIn`/`slotReadV0`/
`eIn_projV0` are y₀-free; `stairMap_abs_det_twoConj` takes a general `D : E →ₗ E`). So we re-derive the
free analogues at the `Dtot`/`BparamsLeaf` level (NOT re-plumbing `eihdT`, which bakes `pbo u` via
`Dtot ha (pbo u)`):
* `eihdT_free ha y₀ := eihdOut ∘ₗ Dtot ha y₀ ∘ₗ eIn.symm` — the flat-Jacobian conjugate at FREE `y₀`.
* `eihdc_free` — the off-diagonal coupling DEFINED from `eihdT_free` (det-invisible).
* `eihdT_J00_free` / `_J01_free` / `_J11_free` — the three block facts at free `y₀` (the same proofs as
  the `pbo u` versions, minus the `set y₀ := pbo u`).
* `eihd_hD_free` — the block identity `eihdOut ∘ Dtot ha y₀ ∘ eIn.symm = stairMap V 2 (eihdF ha y₀) c`.
* `eihdF0_abs_det_free` — the boundary-`0` Schur block det at free `y₀` (`schurFrame_abs_det`, generic),
  no `h0r`/`h0c` (the SchurInc-width positivity is unneeded — `schurFrame_abs_det` is fully generic).
* **`Dtot_abs_det_free`** — `|det (Dtot ha y₀)| = |(Matrix.of (readK … y₀ ⟨0⟩)).det|^(r+c)`, via
  `stairMap_abs_det_twoConj` + the two free block dets, GATED on the y₀-free regauge `hreg`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` target (the keystone + Schur/chain dets;
`hreg` enters only as a hypothesis).
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

section L2

variable {M : Fin (2 + 1) → ℕ}

/-! ## The free boundary-`0` Schur block det

`eihdF ha y₀ 0 = schurFrameDeriv (readX ⟨0⟩) (readK ⟨0⟩) (readN ⟨0⟩)`; its abs-det is `|det K|^(r+c)`
by the fully-generic `schurFrame_abs_det`, with `K = readK ha y₀ ⟨0⟩`. No `h0r`/`h0c` (the SchurInc
widths are formed from `schurT1/R1/C1`, which `eihdF` already carries; the det law is positivity-free). -/

/-- `|det (eihdF ha y₀ 0)| = |(readK … y₀ ⟨0⟩ as a matrix).det|^(r+c)` at a FREE `y₀` — the boundary-`0`
Schur block, via the generic `schurFrame_abs_det`. The `r+c` exponent matches the headline. -/
theorem eihdF0_abs_det_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (eihdF ha y₀ 0)|
      = |(Matrix.of (readK M (tach M) ha y₀ ⟨0, by decide⟩)).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)) := by
  change |LinearMap.det (schurFrameDeriv _ _ _)| = _
  rw [schurFrame_abs_det]
  rfl

/-! ## The free flat-Jacobian conjugate `eihdT_free` and the coupling `eihdc_free` -/

/-- The flat-Jacobian conjugate `eihdT_free ha y₀ := eihdOut ∘ Dtot ha y₀ ∘ eIn.symm` at a FREE `y₀` —
the free-point analogue of `eihdT` (which bakes `pbo u` via `Dtot ha (pbo u)`). -/
noncomputable def eihdT_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    StairProd (eihdV M) 2 →ₗ[ℝ] StairProd (eihdV M) 2 :=
  (eihdOut ha : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2)
    ∘ₗ Dtot ha y₀
    ∘ₗ ((eIn ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))

/-- **Bridge 1 (free)** — `eihdT_free w = packStair (fderiv BparamsLeaf y₀ (eIn.symm w))`. Same proof
as `eihdT_eq_packStair_fderiv`, with the free `y₀`: the `paramsEquivFlatLinear.symm ∘ paramsEquivFlatCLE`
round-trip is the identity, leaving `packStair ∘ (fderiv BparamsLeaf) ∘ eIn.symm`. -/
theorem eihdT_free_eq_packStair_fderiv (ha : StructAdm M (tach M))
    (y₀ : Fin (routeMAmbient M) → ℝ) (w : StairProd (eihdV M) 2) :
    eihdT_free ha y₀ w
      = packStair ha (fderiv ℝ (fun z => BparamsLeaf ha z) y₀ ((eIn ha).symm w)) := by
  show (eihdOut ha) ((Dtot ha _) ((eIn ha).symm w)) = _
  unfold eihdOut Dtot
  rw [LinearEquiv.trans_apply]
  congr 1
  show (paramsEquivFlatLinear M).symm
      ((paramsEquivFlatCLE M) (fderiv ℝ (fun z => BparamsLeaf ha z) _ ((eIn ha).symm w))) = _
  rw [show ⇑(paramsEquivFlatCLE M) = ⇑(paramsEquivFlatLinear M) from by
        rw [paramsEquivFlatCLE_coe, paramsEquivFlatLinear_coe]]
  exact (paramsEquivFlatLinear M).symm_apply_apply _

/-- **The free staircase coupling `eihdc_free`**, DEFINED from the actual off-diagonal block of
`eihdT_free` (the V0→V1 head-into-tail coupling, det-invisible). `c.1 = projTail ∘ T ∘ inclV0`;
`c.2 = (0, ())`. -/
noncomputable def eihdc_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    StairCoupling (eihdV M) 2 :=
  ⟨(LinearMap.snd ℝ (eihdV M 0) (StairProd (fun k => eihdV M (k + 1)) 1)).comp
      ((eihdT_free ha y₀).comp (eihdInclV0 (M := M))),
    ⟨0, PUnit.unit⟩⟩

/-- `eihdc_free.1 v0 = (eihdT_free … (v0, (0, ()))).2` — the coupling reads the tail of `eihdT_free`
along `inclV0`. -/
theorem eihdc_free_fst_apply (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ)
    (v0 : eihdV M 0) :
    (eihdc_free ha y₀).1 v0 = (eihdT_free ha y₀ (v0, (0, PUnit.unit))).2 := rfl

/-! ## The three free block facts (J00 / J01 / J11) -/

/-- **J00 (free)** — the V0→V0 block of `eihdT_free` is `eihdF ha y₀ 0 = schurFrameDeriv X K N`. -/
theorem eihdT_J00_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ)
    (v0 : eihdV M 0) :
    (eihdT_free ha y₀ (v0, (0, PUnit.unit))).1 = eihdF ha y₀ 0 v0 := by
  rw [eihdT_free_eq_packStair_fderiv ha y₀]
  show packLayer0 ha
      ((fderiv ℝ (fun z => BparamsLeaf ha z) y₀ ((eIn ha).symm (v0, (0, PUnit.unit)))) 0) = _
  rw [BparamsLeaf_fderiv_layer ha y₀ _ 0,
    packLayer0_layer0_fderiv ha y₀ ((eIn ha).symm (v0, (0, PUnit.unit)))]
  have hslot : slotReadV0 ha ((eIn ha).symm (v0, (0, PUnit.unit))) = v0 := by
    have h := eIn_projV0 ha ((eIn ha).symm (v0, (0, PUnit.unit)))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  rw [hslot]; rfl

/-- **J01 = 0 (free)** — the V1→V0 block of `eihdT_free` is `0`: the chain coords do not feed the
frame Schur output. -/
theorem eihdT_J01_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ)
    (v1 : eihdV M 1) :
    (eihdT_free ha y₀ (0, (v1, PUnit.unit))).1 = 0 := by
  rw [eihdT_free_eq_packStair_fderiv ha y₀]
  show packLayer0 ha
      ((fderiv ℝ (fun z => BparamsLeaf ha z) y₀ ((eIn ha).symm (0, (v1, PUnit.unit)))) 0) = _
  rw [BparamsLeaf_fderiv_layer ha y₀ _ 0,
    packLayer0_layer0_fderiv ha y₀ ((eIn ha).symm (0, (v1, PUnit.unit)))]
  have hslot : slotReadV0 ha ((eIn ha).symm (0, (v1, PUnit.unit))) = 0 := by
    have h := eIn_projV0 ha ((eIn ha).symm (0, (v1, PUnit.unit)))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  rw [hslot]; exact map_zero _

/-- **J11 (free)** — the V1→V1 block of `eihdT_free` is `eihdF ha y₀ 1 = chainUnitMap (readN ⟨0⟩)`:
the layer-1 chaining `(W, C) ↦ (W, C − N·W)`. -/
theorem eihdT_J11_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ)
    (v1 : eihdV M 1) :
    (eihdT_free ha y₀ (0, (v1, PUnit.unit))).2.1 = eihdF ha y₀ 1 v1 := by
  rw [eihdT_free_eq_packStair_fderiv ha y₀]
  show packLayer1 ha
      ((fderiv ℝ (fun z => BparamsLeaf ha z) y₀ ((eIn ha).symm (0, (v1, PUnit.unit)))) 1) = _
  rw [BparamsLeaf_fderiv_layer ha y₀ _ 1, packLayer1_fderiv ha y₀ _]
  set d := (eIn ha).symm (0, (v1, PUnit.unit)) with hd
  have hV1 : ((matrixReaderCLM (fun i j => readW0_idx ha i j)) d,
       (matrixReaderCLM (fun i j => leaf_idx ha i j)) d) = v1 := by
    rw [dWdC_eq_eInV1, hd, LinearEquiv.apply_symm_apply]
  have hW : (matrixReaderCLM (fun i j => readW0_idx ha i j)) d = v1.1 := by rw [← hV1]
  have hC : (matrixReaderCLM (fun i j => leaf_idx ha i j)) d = v1.2 := by rw [← hV1]
  have hslot0 : slotReadV0 ha d = 0 := by
    have h := eIn_projV0 ha d
    rw [hd, LinearEquiv.apply_symm_apply] at h
    rw [← h]; rfl
  have hN : (matrixReaderCLM (fun i j => readN0_idx ha i j)) d = 0 := by
    show (slotReadV0 ha d).2.1 = 0
    rw [hslot0]; rfl
  rw [hW, hC, hN, Matrix.zero_mul, add_zero]
  show (v1.1, v1.2 - (Nfun ha y₀) * v1.1) = _
  rfl

/-- **`eihd_hD_free` — the block identity at FREE `y₀`**: `eihdOut ∘ Dtot ha y₀ ∘ eIn.symm =
stairMap V 2 (eihdF ha y₀) c`, assembled from the three free block facts (J00/J01/J11) with `c` the
off-diagonal coupling. Same `LinearMap.ext` assembly as `eihd_hD`, free `y₀`. -/
theorem eihd_hD_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    (eihdOut ha : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2)
        ∘ₗ Dtot ha y₀
        ∘ₗ ((eIn ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
      = stairMap (eihdV M) 2 (eihdF ha y₀) (eihdc_free ha y₀) := by
  apply LinearMap.ext
  rintro ⟨v0, v1, ⟨⟩⟩
  have hT : ((eihdOut ha : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2)
        ∘ₗ Dtot ha y₀
        ∘ₗ ((eIn ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ)))
          (v0, (v1, PUnit.unit))
      = eihdT_free ha y₀ (v0, (v1, PUnit.unit)) := rfl
  rw [hT]
  have hsplit : ((v0, (v1, PUnit.unit)) : StairProd (eihdV M) 2)
      = (v0, ((0 : eihdV M 1), PUnit.unit)) + (0, (v1, PUnit.unit)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show v0 = v0 + 0; exact (add_zero v0).symm
    · show v1 = 0 + v1; exact (zero_add v1).symm
    · rfl
  have happ : eihdT_free ha y₀ (v0, (v1, PUnit.unit))
      = eihdT_free ha y₀ (v0, ((0 : eihdV M 1), PUnit.unit))
        + eihdT_free ha y₀ (0, (v1, PUnit.unit)) := by
    rw [hsplit]; exact map_add _ _ _
  rw [happ]
  set f := eihdF ha y₀ with hf
  set c := eihdc_free ha y₀ with hc
  show eihdT_free ha y₀ (v0, (0, PUnit.unit)) + eihdT_free ha y₀ (0, (v1, PUnit.unit))
      = (f 0 v0, ((f 1 v1 + (c.1 v0).1), (c.1 v0).2))
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (eihdT_free ha y₀ (v0, (0, PUnit.unit))).1
        + (eihdT_free ha y₀ (0, (v1, PUnit.unit))).1 = f 0 v0
    rw [eihdT_J00_free ha y₀ v0, eihdT_J01_free ha y₀ v1, add_zero]
  · show (eihdT_free ha y₀ (v0, (0, PUnit.unit))).2.1
        + (eihdT_free ha y₀ (0, (v1, PUnit.unit))).2.1 = f 1 v1 + (c.1 v0).1
    rw [eihdT_J11_free ha y₀ v1, add_comm]
    rfl
  · rfl

/-! ## The headline: `Dtot_abs_det_free` -/

/-- **`Dtot_abs_det_free`** — the FREE-`y₀` boundary-factor determinant. Given the y₀-free regauge
abs-det-`1` `hreg : |det ((eihdOut).symm ∘ eIn)| = 1`, the determinant of `Dtot ha y₀` is the free-K
Schur value `|det K|^(r+c)` with `K = readK … y₀ ⟨0⟩` and `(r, c) = (Text1−Text2, Wext1−Text2)` —
the free-point generalization of `RouteMHDtotConj.hDtot_of_twoStairConj` (which fixes `y₀ = pbo u`).
Factor 1 of genm-ambdet's `BdetMonomial` chain-rule (instantiated at `y₀ = Z = kLDU (pbo u)`).

Via the point-free keystone `stairMap_abs_det_twoConj` on the free block identity `eihd_hD_free`, with
the two diagonal-block dets (`eihdF0_abs_det_free` = `|det K|^(r+c)`, `eihdF1_abs_det` = `1`). -/
theorem Dtot_abs_det_free (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ)
    (hreg : |LinearMap.det
        (((eihdOut ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
          ∘ₗ ((eIn ha) : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2))| = 1) :
    |LinearMap.det (Dtot ha y₀)|
      = |(Matrix.of (readK M (tach M) ha y₀ ⟨0, by decide⟩)).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)) := by
  rw [stairMap_abs_det_twoConj (eihdV M) 2 (eihdF ha y₀) (eihdc_free ha y₀) (eIn ha) (eihdOut ha)
        (Dtot ha y₀) (eihd_hD_free ha y₀) hreg, Fin.prod_univ_two]
  show |LinearMap.det (eihdF ha y₀ 0)| * |LinearMap.det (eihdF ha y₀ 1)| = _
  rw [eihdF0_abs_det_free ha y₀, eihdF1_abs_det ha y₀, mul_one]

end L2

end DLNFibre.DLN.RLCT

end
