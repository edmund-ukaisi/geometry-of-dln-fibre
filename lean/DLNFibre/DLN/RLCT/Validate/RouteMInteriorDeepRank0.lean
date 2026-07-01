import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveContract
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveAtom
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareReduce

/-!
# `RouteMInteriorDeepRank0` — the `deepRank = 0` interior achiever handler (L = 2)

The LIVE-leaf ∘ kLDU interior atom (`routeMCore_box_diverges_interiorLive`, `RouteMInteriorLiveAtom`)
covers `InteriorDrop ∧ 0 < deepRank` — its chart binds `leafPivot`, which needs `h0r : 0 < Text 2`
(= `0 < deepRank`). At `deepRank = 0` (a genuine interior stratum, e.g. `M = (1,1,2)`: unique
`tStar = ![0,0]`, `interiorDrop_L2_iff` ⟹ InteriorDrop, `minAdm = M0·M1 = 1`) the leaf K-block is
VACUOUS (`activeLeafImg.card = Text 2 · Wext 2 = 0`) and the codimension lives ENTIRELY in the front
E-block (`activeEImg.card = (Text1 − 0)(Wext1 − 0) = M0·M1 = minAdm`).

**The handler is an E-BLOCK radial blow-up.** The binding pivot is the E-block `(0,0)` slot
`eBlockPivot`; the radial axis `u = x eBlockPivot` scales the front E-block. The chart GAUGE-FIXES the
pivot E-slot to `1` (the E-block analogue of `rfinFixedPivot`'s leaf `(0,0) = 1`) so the pivot slot is
NOT double-counted (it is the radial axis, not a free residual). The non-pivot E-slots stay live. This
is the `deepRank = 0` fix of the naïve `phiFlatLiveAt … eBlockPivot` chart, whose direct `readE` would
read the pivot slot as a free residual AND scale it by the radial, giving `(x_p)²` in the map and an
extra `|u_p|` in the det (the Item-102 double-count trap).

At `deepRank = 0` every K-block vanishes (boundary 0's K is `Text 2 = 0`-dim, the leaf's is `Text 3 =
0`-dim), so there is no LDU-core / Schur-frame exponent: the boundary factor `B` (the radial-`1` chart
reading the E-block directly) is a LINEAR coordinate reshape with `|det DB| = 1`. So the chart Jacobian
abs-det is the PURE single-axis monomial `|u_{eBlockPivot}|^{minAdm−1}` (NO K-product), and the
box-divergence threshold is `½·minAdm = ½·M0·M1` — EXACTLY the headline rate (kill-condition verified:
Codex xhigh + the `rBlock·cBlock` budget).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin (2 + 1) → ℕ}

/-! ## The E-block pivot + the deepRank = 0 hypotheses -/

/-- **The E-block (0,0) pivot** at the interior boundary `⟨0⟩`, the radial binding axis at
`deepRank = 0`. Needs `0 < Text 1 − Text 2` and `0 < Wext 1 − Text 2` (at `deepRank = 0`: `0 < M0`,
`0 < M1`, from `widths_pos_of_minAdm`). -/
noncomputable def eBlockPivot (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    Fin (routeMAmbient M) :=
  activeSlotE M (tach M) ha ⟨0, by decide⟩ ⟨0, hr⟩ ⟨0, hc⟩

/-- **`eBlockPivot ∈ activeM`** (in the E-image, hence the active set). -/
theorem eBlockPivot_mem_activeM (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    eBlockPivot ha hr hc ∈ activeM M ha :=
  activeSlotE_mem_activeM ha ⟨0, hr⟩ ⟨0, hc⟩

/-- At `deepRank = 0` the pivot-boundary row/col drops are trivial (`Text 2 = 0`). -/
theorem eDrop_row (hdr0 : Text M (tach M) 2 = 0) : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1 := by
  rw [show (1 : ℕ) + 1 = 2 from rfl, hdr0]; exact Nat.zero_le _

/-- At `deepRank = 0` the pivot-boundary col drop is trivial (`Text 2 = 0`). -/
theorem eDrop_col (hdr0 : Text M (tach M) 2 = 0) : Text M (tach M) (1 + 1) ≤ Wext M 1 := by
  rw [show (1 : ℕ) + 1 = 2 from rfl, hdr0]; exact Nat.zero_le _

/-! ## The E-fixed-pivot reader + decoder (the `deepRank = 0` gauge-fixed E-radial chart) -/

/-- **The E-fixed-pivot reader** — the E-block residual with the pivot `(0,0)` entry pinned to the
radial fixed `1`, and the other entries read from `x` via `readE`. The E-block analogue of the leaf
`rfinFixedPivot`: at the radial axis the chart carries the literal `1`, so the radial scalar `u`
multiplies a fixed direction (no double-count), and the off-pivot E-slots stay live residual. -/
noncomputable def EfixedReader (ha : StructAdm M (tach M)) (x : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
      (Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))) ℝ :=
  Matrix.of fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 else readE M (tach M) ha x ⟨0, by decide⟩ i j

/-- **The E-fixed-pivot decoder** `genBlkFlatEfp` — the live decoder with the pivot boundary `1`'s
`Rmat` overridden to `rmatPad (EfixedReader x)` (via `Function.update`, exactly as `genBlkFlatLiveR1`
overrides with `pivotEIndicator`, but here the OTHER E-slots stay live). All other blocks and the
identity boundary are as in `genBlkFlatLive`. -/
noncomputable def genBlkFlatEfp (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) : GenBlk M (tach M) where
  Bmat := (genBlkFlatLive M (tach M) ha 0 x).Bmat
  Nblk := (genBlkFlatLive M (tach M) ha 0 x).Nblk
  Wblk := (genBlkFlatLive M (tach M) ha 0 x).Wblk
  Rmat := Function.update (genBlkFlatLive M (tach M) ha 0 x).Rmat 1
    (rmatPad M (tach M) 1 hp1 hp2 (EfixedReader ha x)
      : Matrix (Fin (Text M (tach M) 1)) (Fin (Wext M 1)) ℝ)
  Rfin := (genBlkFlatLive M (tach M) ha 0 x).Rfin

/-- The Efp decoder's identity boundary `Rmat 0 = 0` (`Function.update` at `1` misses `0`). -/
theorem genBlkFlatEfp_Rmat0 (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfp ha hp1 hp2 x).Rmat 0 = (0 : Matrix (Fin (Text M (tach M) 0)) (Fin (Wext M 0)) ℝ) := by
  have h : (genBlkFlatEfp ha hp1 hp2 x).Rmat 0
      = Function.update (genBlkFlatLive M (tach M) ha 0 x).Rmat 1
          (rmatPad M (tach M) 1 hp1 hp2 (EfixedReader ha x)) 0 := rfl
  rw [h, Function.update_of_ne (by norm_num)]
  exact genBlkFlatLive_Rmat0 M (tach M) ha 0 x

/-- The Efp decoder's `Bmat 0` is the identity boundary's `reindex 1` (inherited from the live/struct
decoder). -/
theorem genBlkFlatEfp_Bmat0 (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfp ha hp1 hp2 x).Bmat 0
      = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M (tach M) ha.h0))
          (1 : Matrix (Fin (Text M (tach M) 0)) (Fin (Text M (tach M) 0)) ℝ) := rfl

/-- **The identity boundary `C 0 = 1`** for the Efp decoder — reads only `Bmat 0`/`Rmat 0`, both as in
the live decoder (`Bmat 0 = reindex 1`; `Rmat 0 = 0` since the `Function.update` at `1` misses `0`).
Proof verbatim from `C0_eq_one_liveR1`. -/
theorem C0_eq_one_Efp (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M (tach M) (genBlkFlatEfp ha hp1 hp2 x) (hleStruct M (tach M) ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M (tach M) 0)) (Fin (Text M (tach M) 0)) ℝ) := by
  rw [chainOfMt_C_zero v M (tach M) _ (hleStruct M (tach M) ha) ha.hL,
    genBlkFlatEfp_Rmat0 ha hp1 hp2 x, smul_zero, add_zero]
  have h1W : Text M (tach M) 1 = Wext M 0 := Wext0_eq_Text1 M (tach M) ha
  rw [genBlkFlatEfp_Bmat0 ha hp1 hp2 x]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Text0_eq_Text1_struct M (tach M) ha.h0) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M 0)) = Fin.cast (genWidthEq M (tach M) (hleStruct M (tach M) ha) 0 ha.hL)
        (Fin.castAdd (Wext M 0 - Text M (tach M) (0 + 1)) (Fin.cast h1W.symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M (tach M) 0)) (Fin (Text M (tach M) 0)) ℝ) i
          (Fin.cast (Text0_eq_Text1_struct M (tach M) ha.h0).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for the Efp decoder** (`C 0 · suffix = suffix` from `C 0 = 1`). -/
theorem hC0_Efp (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M (tach M) (genBlkFlatEfp ha hp1 hp2 x) (hleStruct M (tach M) ha)).toChain.C 0
        * (chainOfMt v M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
            (hleStruct M (tach M) ha)).toChain.suffix 0 (Nat.zero_le 2)
      = (chainOfMt v M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
          (hleStruct M (tach M) ha)).toChain.suffix 0 (Nat.zero_le 2) := by
  rw [C0_eq_one_Efp ha hp1 hp2 v x]; exact Matrix.one_mul _

/-! ## The deepRank = 0 chart + its rate -/

/-- **The deepRank = 0 chart** `eDeepRank0Phi := phiGen (x eBlockPivot) M tach (genBlkFlatEfp x)` — the
E-block radial blow-up with the pivot E-slot gauge-fixed to `1`. -/
noncomputable def eDeepRank0Phi (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  fun x => phiGen (x (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
    (hleStruct M (tach M) ha)

/-- **The deepRank = 0 rate** `routeMCore M (φ₀ x) = (x eBlockPivot)²·V` — the decoder-agnostic rate
`routeMCore_phiGen` at radial `x eBlockPivot`, via the Efp identity-boundary `hC0_Efp`. -/
theorem eDeepRank0Phi_rate (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (eDeepRank0Phi ha hr hc hp1 hp2 x)
      = (x (eBlockPivot ha hr hc)) ^ 2
        * VvalGen (x (eBlockPivot ha hr hc)) M (tach M)
            (genBlkFlatEfp ha hp1 hp2 x) (hleStruct M (tach M) ha) :=
  routeMCore_phiGen (x (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
    (hleStruct M (tach M) ha) (hC0_Efp ha hp1 hp2 (x (eBlockPivot ha hr hc)) x)

/-! ## The single-axis Jacobian exponent vector (pure radial: `minAdm−1` at the pivot, `0` else) -/

/-- **The deepRank = 0 Jacobian exponent vector** — SINGLE-AXIS: `minAdm − 1` on the binding E-pivot,
`0` on every other coordinate. At `deepRank = 0` the chart is a pure radial blow-up of the E-block
(all K-blocks vanish, so no LDU-core / Schur-frame exponent; the boundary factor is a linear coordinate
reshape with `|det| = 1`); the only Jacobian weight is the radial `|u_{eBlockPivot}|^{minAdm−1}`. -/
noncomputable def eDeepRank0_leafH (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    Fin (routeMAmbient M) → ℕ := fun j =>
  if j = eBlockPivot ha hr hc then minAdm M - 1 else 0

/-- **The binding axis carries `minAdm − 1`** (`if_pos rfl`). -/
theorem eDeepRank0_leafH_pivot (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    eDeepRank0_leafH ha hr hc (eBlockPivot ha hr hc) = minAdm M - 1 := by
  rw [eDeepRank0_leafH, if_pos rfl]

/-! ## Item 5 — the E-block determinant

The chart factors as `eDeepRank0Phi = B ∘ pivotBlowupOn activeM eBlockPivot`, where `B` is the
radial-`1` boundary factor reading the E-block DIRECTLY (the plain live decoder, `readE`). The
pivot-generic radial wiring `radialComp_abs_det_at` then gives
`|det Dφ| = |u eBlockPivot|^{minAdm−1} · |det DB|`; at `deepRank = 0` there is no K-block, so `B` is a
LINEAR coordinate reshape with `|det DB| = 1`, hence the pure single-axis monomial. -/

/-- **The boundary-factor chart parameters** `BparamsE ha y : Params M` — the radial-`1` chart reading
the E-block DIRECTLY (the plain `genBlkFlatLive` at radial `1`, leaf residual `0` since the leaf is
0-dim at `deepRank = 0`). -/
noncomputable def BparamsE (ha : StructAdm M (tach M)) (y : Fin (routeMAmbient M) → ℝ) :
    Params M :=
  chartParamsGen 1 M (tach M) (genBlkFlatLive M (tach M) ha 0 y) (hleStruct M (tach M) ha)

/-- **The boundary factor** `BchartE ha y := paramsEquivFlat M (BparamsE ha y)`. -/
noncomputable def BchartE (ha : StructAdm M (tach M)) (y : Fin (routeMAmbient M) → ℝ) :
    Fin (routeMAmbient M) → ℝ :=
  paramsEquivFlat M (BparamsE ha y)

/-! ### Spectator readers are fixed by `pivotBlowupOn (activeM) eBlockPivot` -/

/-- A chartIdx-`⟨0⟩` non-E-tag slot is `≠ eBlockPivot` (`eBlockPivot ∈ activeM`, the slot `∉ activeM`). -/
theorem boundary0_ne_eBlockPivot (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (tag : Fin (schurDim M (tDesc M (tach M)) 0) ⊕ Fin (liftDim M (tDesc M (tach M)) 0))
    (hne : ∀ (iE : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
        (jE : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))),
        tag ≠ Sum.inl ((frameSplitEquiv M (tach M) (0 + 1)
          (ha.hdesc 0 (by decide)) (ha.hub 0)).symm (Sum.inr (finProdFinEquiv (iE, jE))))) :
    (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩
      ≠ eBlockPivot ha hr hc := by
  intro h
  exact boundary0_notMem_activeM ha tag hne (h ▸ eBlockPivot_mem_activeM ha hr hc)

/-- **`pivotBlowupOn (activeM) eBlockPivot` fixes a chartIdx-`⟨0⟩` non-E slot** (`≠ eBlockPivot` and
`∉ activeM`). -/
theorem pboE_fixes_boundary0 (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (tag : Fin (schurDim M (tDesc M (tach M)) 0) ⊕ Fin (liftDim M (tDesc M (tach M)) 0))
    (hne : ∀ (iE : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
        (jE : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))),
        tag ≠ Sum.inl ((frameSplitEquiv M (tach M) (0 + 1)
          (ha.hdesc 0 (by decide)) (ha.hub 0)).symm (Sum.inr (finProdFinEquiv (iE, jE)))))
    (x : Fin (routeMAmbient M) → ℝ) :
    pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x
        ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩)
      = x ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨⟨0, by decide⟩, tag⟩) := by
  unfold pivotBlowupOn
  rw [if_neg (boundary0_ne_eBlockPivot ha hr hc tag hne),
    if_neg (boundary0_notMem_activeM ha tag hne)]

/-- `readK` at boundary `⟨0⟩` is fixed by `pivotBlowupOn (activeM) eBlockPivot`. -/
theorem readK_pboE (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (x : Fin (routeMAmbient M) → ℝ) (i j : Fin (Text M (tach M) (0 + 2))) :
    readK M (tach M) ha (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x) ⟨0, by decide⟩ i j
      = readK M (tach M) ha x ⟨0, by decide⟩ i j := by
  rw [readK, readK]
  exact pboE_fixes_boundary0 ha hr hc _ (fun iE jE h => by
    have := (frameSplitEquiv M (tach M) (0 + 1) (ha.hdesc 0 (by decide)) (ha.hub 0)).symm.injective
      (Sum.inl.inj h); exact Sum.inl_ne_inr this) x

/-- `readX` at boundary `⟨0⟩` is fixed by `pivotBlowupOn (activeM) eBlockPivot`. -/
theorem readX_pboE (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2))) (j : Fin (Text M (tach M) (0 + 2))) :
    readX M (tach M) ha (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x) ⟨0, by decide⟩ i j
      = readX M (tach M) ha x ⟨0, by decide⟩ i j := by
  rw [readX, readX]
  exact pboE_fixes_boundary0 ha hr hc _ (fun iE jE h => by
    have := (frameSplitEquiv M (tach M) (0 + 1) (ha.hdesc 0 (by decide)) (ha.hub 0)).symm.injective
      (Sum.inl.inj h); exact Sum.inl_ne_inr this) x

/-- `readN` at boundary `⟨0⟩` is fixed by `pivotBlowupOn (activeM) eBlockPivot`. -/
theorem readN_pboE (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) (0 + 2))) (j : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))) :
    readN M (tach M) ha (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x) ⟨0, by decide⟩ i j
      = readN M (tach M) ha x ⟨0, by decide⟩ i j := by
  rw [readN, readN]
  exact pboE_fixes_boundary0 ha hr hc _ (fun iE jE h => by
    have := (frameSplitEquiv M (tach M) (0 + 1) (ha.hdesc 0 (by decide)) (ha.hub 0)).symm.injective
      (Sum.inl.inj h); exact Sum.inl_ne_inr this) x

/-- `readW` at boundary `⟨0⟩` is fixed by `pivotBlowupOn (activeM) eBlockPivot` (the `W`-tag is the
lift `Sum.inr` summand, distinct from the `Sum.inl` frame E-tag). -/
theorem readW_pboE (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hk2 : (0 : ℕ) + 1 < 2) (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))) (j : Fin (Wext M (0 + 2))) :
    readW M (tach M) ha (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x) ⟨0, by decide⟩ hk2 i j
      = readW M (tach M) ha x ⟨0, by decide⟩ hk2 i j := by
  rw [readW, readW]
  exact pboE_fixes_boundary0 ha hr hc _ (fun iE jE h => Sum.inl_ne_inr h.symm) x

/-- A non-pivot E-slot `(i,j) ≠ (0,0)` is `≠ eBlockPivot` (`activeSlotE` injective in `(i,j)`). -/
theorem activeSlotE_ne_eBlockPivot (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (i : Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
    (j : Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))) (hij : ¬ (i.val = 0 ∧ j.val = 0)) :
    activeSlotE M (tach M) ha ⟨0, by decide⟩ i j ≠ eBlockPivot ha hr hc := by
  rw [eBlockPivot]
  intro h
  obtain ⟨hi, hj⟩ := activeSlotE_inj M (tach M) ha ⟨0, by decide⟩ h
  exact hij ⟨by simp [hi], by simp [hj]⟩

/-- **The E-fixed-pivot radial identity** — the load-bearing entry-wise match on the E-block:
`(x eBlockPivot) • EfixedReader x = readE (pbo x) ⟨0⟩` (as matrices). At the pivot `(0,0)`:
`(x p₀)·1 = (pbo x) p₀ = x p₀ = readE (pbo x) @pivot` (pbo fixes the pivot); off `(0,0)`:
`(x p₀)·(readE x) = (pbo x)(activeSlotE i j) = readE (pbo x)` (pbo scales the active non-pivot E-slot). -/
theorem EfixedReader_pboE (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (x : Fin (routeMAmbient M) → ℝ) :
    (x (eBlockPivot ha hr hc)) • EfixedReader ha x
      = (fun i j => readE M (tach M) ha
          (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x) ⟨0, by decide⟩ i j) := by
  funext i j
  rw [Matrix.smul_apply, smul_eq_mul, EfixedReader, Matrix.of_apply]
  -- both readE slots ARE `x (activeSlotE ⟨0⟩ i j)` (defeq)
  have hslot : readE M (tach M) ha (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x)
        ⟨0, by decide⟩ i j
      = pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x
          (activeSlotE M (tach M) ha ⟨0, by decide⟩ i j) := rfl
  rw [hslot]
  by_cases hij : i.val = 0 ∧ j.val = 0
  · -- the pivot entry: LHS `= x p₀ · 1`; RHS `= (pbo x) p₀ = x p₀`
    obtain ⟨hi, hj⟩ := hij
    have hi' : i = ⟨0, hr⟩ := Fin.ext hi
    have hj' : j = ⟨0, hc⟩ := Fin.ext hj
    subst hi' hj'
    rw [if_pos ⟨rfl, rfl⟩, mul_one]
    change x (eBlockPivot ha hr hc) = pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x
      (activeSlotE M (tach M) ha ⟨0, by decide⟩ ⟨0, hr⟩ ⟨0, hc⟩)
    rw [show activeSlotE M (tach M) ha ⟨0, by decide⟩ ⟨0, hr⟩ ⟨0, hc⟩ = eBlockPivot ha hr hc from rfl,
      pivotBlowupOn, if_pos rfl]
  · -- a non-pivot E-entry: LHS `= x p₀ · readE x`; RHS `= (pbo x)(slot) = x p₀ · x slot`
    rw [if_neg hij]
    have hslotx : readE M (tach M) ha x ⟨0, by decide⟩ i j
        = x (activeSlotE M (tach M) ha ⟨0, by decide⟩ i j) := rfl
    rw [hslotx, pivotBlowupOn, if_neg (activeSlotE_ne_eBlockPivot ha hr hc i j hij),
      if_pos (activeSlotE_mem_activeM ha i j)]

/-! ### The Cgen match between the chart decoder (Efp) and the B decoder (direct) -/

/-- The Efp decoder's `Bmat`/`Nblk` at the interior boundary `1` are the live/struct decoder's. -/
theorem genBlkFlatEfp_Bmat1 (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfp ha hp1 hp2 x).Bmat (0 + 1)
      = bmatStack M (tach M) (0 + 1) (ha.hdesc 0 (by decide))
          (readK M (tach M) ha x ⟨0, by decide⟩) (readX M (tach M) ha x ⟨0, by decide⟩) :=
  genBlkFlatLive_Bmat_succ M (tach M) ha 0 x 0 (by decide)

theorem genBlkFlatEfp_Nblk1 (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfp ha hp1 hp2 x).Nblk (0 + 1) = readN M (tach M) ha x ⟨0, by decide⟩ :=
  genBlkFlatLive_Nblk_succ M (tach M) ha 0 x 0 (by decide)

/-- The Efp decoder's `Rmat` at the pivot boundary `1` IS `rmatPad (EfixedReader x)`. -/
theorem genBlkFlatEfp_Rmat1 (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfp ha hp1 hp2 x).Rmat 1 = rmatPad M (tach M) 1 hp1 hp2 (EfixedReader ha x) := by
  have h : (genBlkFlatEfp ha hp1 hp2 x).Rmat 1
      = Function.update (genBlkFlatLive M (tach M) ha 0 x).Rmat 1
          (rmatPad M (tach M) 1 hp1 hp2 (EfixedReader ha x)) 1 := rfl
  rw [h, Function.update_self]

/-- **The Efp-decoder interior `Cgen = schurFrameProd`** at boundary `1` with `E = EfixedReader`. -/
theorem Cgen_Efp_interior (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    Cgen v M (tach M) (genBlkFlatEfp ha hp1 hp2 x) (hleStruct M (tach M) ha) (0 + 1)
      = schurFrameProd M (tach M) (0 + 1) (ha.hdesc 0 (by decide)) (ha.hub 0) v
          (readK M (tach M) ha x ⟨0, by decide⟩) (readX M (tach M) ha x ⟨0, by decide⟩)
          (readN M (tach M) ha x ⟨0, by decide⟩) (EfixedReader ha x) := by
  rw [Cgen, dif_pos (by decide : (0 : ℕ) + 1 < 2), genBlkFlatEfp_Bmat1 ha hp1 hp2 x,
    genBlkFlatEfp_Nblk1 ha hp1 hp2 x, genBlkFlatEfp_Rmat1 ha hp1 hp2 x, schurFrameProd]

/-- **The interior `Cgen 1` match**: the chart's interior transition (radial `x p₀`, E-pivot fixed via
`EfixedReader`) equals the `B`-decoder's (radial `1`, E read directly from `pbo x`). Both are the Schur
frame; K/X/N are spectator reads (fixed via `read{K,X,N}_pboE`), and the radial `x p₀` moves into the
residual coordinate (`schurFrameProd_u_to_E` + `EfixedReader_pboE`). -/
theorem Cgen1_match_E (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    Cgen (x (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
        (hleStruct M (tach M) ha) (0 + 1)
      = Cgen 1 M (tach M)
          (genBlkFlatLive M (tach M) ha 0
            (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x))
          (hleStruct M (tach M) ha) (0 + 1) := by
  set p₀ := eBlockPivot ha hr hc with hp₀
  set pbo := pivotBlowupOn (activeM M ha) p₀ with hpbo
  rw [Cgen_Efp_interior ha hp1 hp2 (x p₀) x,
    Cgen_live_interior_eq_schurFrameProd M (tach M) ha 0 1 (pbo x) 0 (by decide),
    schurFrameProd_u_to_E M (tach M) (0 + 1) _ _ (x p₀)]
  congr 1
  · funext i j; exact (readK_pboE ha hr hc x i j).symm
  · funext i j; exact (readX_pboE ha hr hc x i j).symm
  · funext i j; exact (readN_pboE ha hr hc x i j).symm
  · rw [EfixedReader_pboE ha hr hc x]

/-- The Efp decoder's leaf `Cgen … 2 = v • Rfin 2` (`dif_neg`; the leaf residual is `genBlkFlatLive`'s
`rfin = 0`). -/
theorem Cgen_Efp_leaf (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    Cgen v M (tach M) (genBlkFlatEfp ha hp1 hp2 x) (hleStruct M (tach M) ha) 2
      = v • (genBlkFlatLive M (tach M) ha 0 x).Rfin 2 := by
  rw [Cgen, dif_neg (by decide : ¬ (2 : ℕ) < 2)]
  rfl

/-- **The leaf `Cgen 2` match** — both sides `= 0` (the leaf residual is `0`, `Text 2 = 0` / `rfin = 0`).
The chart's `(x p₀) • 0` and the `B`-decoder's `1 • 0` are equal. -/
theorem Cgen2_match_E (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    Cgen (x (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
        (hleStruct M (tach M) ha) 2
      = Cgen 1 M (tach M)
          (genBlkFlatLive M (tach M) ha 0
            (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x))
          (hleStruct M (tach M) ha) 2 := by
  rw [Cgen_Efp_leaf ha hp1 hp2 (x (eBlockPivot ha hr hc)) x,
    Cgen_live_leaf M (tach M) ha 0 1 (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x),
    smul_zero]
  have hRfin : (genBlkFlatLive M (tach M) ha 0 x).Rfin 2
      = (0 : Matrix (Fin (Text M (tach M) 2)) (Fin (Wext M 2)) ℝ) := by
    simp only [genBlkFlatLive, dif_pos]
  rw [hRfin, smul_zero]

/-! ### The `Nblk`/`Wblk` spectator matches + the chart-parameter match + `hmap` -/

/-- The Efp `Nblk (0+1)` (`= readN`) matches the B decoder's (spectator, fixed by `pboE`). -/
theorem live_Nblk_match_E (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfp ha hp1 hp2 x).Nblk (0 + 1)
      = (genBlkFlatLive M (tach M) ha 0
          (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x)).Nblk (0 + 1) := by
  rw [genBlkFlatEfp_Nblk1 ha hp1 hp2 x,
    genBlkFlatLive_Nblk_succ M (tach M) ha 0 _ 0 (by decide)]
  funext i j; exact (readN_pboE ha hr hc x i j).symm

/-- The Efp `Wblk (0+1)` matches the B decoder's (spectator, fixed by `pboE`). -/
theorem live_Wblk_match_E (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatEfp ha hp1 hp2 x).Wblk (0 + 1)
      = (genBlkFlatLive M (tach M) ha 0
          (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x)).Wblk (0 + 1) := by
  show (genBlkFlatStruct M (tach M) ha x).Wblk (0 + 1)
    = (genBlkFlatStruct M (tach M) ha
        (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x)).Wblk (0 + 1)
  simp only [genBlkFlatStruct, dif_pos (show (0 : ℕ) < 2 by decide),
    dif_pos (show 0 + 1 < 2 by decide)]
  funext i j; exact (readW_pboE ha hr hc (by decide) x i j).symm

/-- **The chart-parameter match** `chartParamsGen (x p₀) … (Efp decoder) = BparamsE (pbo x)` — the
genuine content of `hmap`, per layer `s : Fin 2`. Both are `reindex (Agen … s.val)`; `Agen_congr`
reduces each to the `Nblk`/`Wblk`/`Cgen(k+1)` matches. Boundary `0` uses the interior `Cgen 1`
(`Cgen1_match_E`); boundary `1` uses the leaf `Cgen 2` (`Cgen2_match_E`). -/
theorem chartParamsGen_match_E (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    chartParamsGen (x (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
        (hleStruct M (tach M) ha)
      = BparamsE ha (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) x) := by
  set p₀ := eBlockPivot ha hr hc with hp₀
  set pbo := pivotBlowupOn (activeM M ha) p₀ with hpbo
  funext s
  show Matrix.reindex _ _ (Agen (x p₀) M (tach M) _ (hleStruct M (tach M) ha) s.val)
    = Matrix.reindex _ _ (Agen 1 M (tach M) _ (hleStruct M (tach M) ha) s.val)
  congr 1
  fin_cases s
  · -- boundary 0: `Agen 0` uses `Nblk 0 = 0` (rfl) + the interior `Cgen 1` match
    exact Agen_congr M (tach M) (hleStruct M (tach M) ha) (x p₀) 1 _ _ 0
      (by rfl) (by rfl) (Cgen1_match_E ha hr hc hp1 hp2 x)
  · -- boundary 1: `Agen 1` uses `Nblk 1 = readN` (the `_pboE` match) + the leaf `Cgen 2` match
    exact Agen_congr M (tach M) (hleStruct M (tach M) ha) (x p₀) 1 _ _ 1
      (live_Nblk_match_E ha hr hc hp1 hp2 x) (live_Wblk_match_E ha hr hc hp1 hp2 x)
      (Cgen2_match_E ha hr hc hp1 hp2 x)

/-- **`hmap`** — `eDeepRank0Phi = BchartE ∘ pivotBlowupOn activeM eBlockPivot` (the map identity, from
the per-layer `chartParamsGen_match_E`). Both sides are `paramsEquivFlat ∘ chartParamsGen`. -/
theorem hmap_E (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1) :
    eDeepRank0Phi ha hr hc hp1 hp2
      = BchartE ha ∘ pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) := by
  funext x
  show phiGen (x (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
      (hleStruct M (tach M) ha) = _
  show paramsEquivFlat M
      (chartParamsGen (x (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 x)
        (hleStruct M (tach M) ha)) = _
  rw [chartParamsGen_match_E ha hr hc hp1 hp2 x]
  rfl

/-! ### `hasDB` — `BchartE` is differentiable (the chain is polynomial in `y`, radial `1`) -/

/-- The `genBlkFlatLive`-`0` decoder's `Cgen` (radial `1`) is differentiable at each `k` (the leaf
residual is the constant `0`). Mirrors `diffAt_Cgen_live` with the `rfinDirect` leaf replaced by `0`. -/
theorem diffAt_Cgen_E (ha : StructAdm M (tach M)) (u : Fin (routeMAmbient M) → ℝ) (k : ℕ) :
    DifferentiableAt ℝ
      (fun y => Cgen (1 : ℝ) M (tach M)
        (genBlkFlatLive M (tach M) ha 0 y) (hleStruct M (tach M) ha) k) u := by
  by_cases hk : k < 2
  · rw [show (fun y => Cgen (1 : ℝ) M (tach M)
          (genBlkFlatLive M (tach M) ha 0 y) (hleStruct M (tach M) ha) k)
        = fun y => (genBlkFlatLive M (tach M) ha 0 y).Bmat k
            * chainQ (genWidthEq M (tach M) (hleStruct M (tach M) ha) k hk)
              ((genBlkFlatLive M (tach M) ha 0 y).Nblk k)
            + (1 : ℝ) • (genBlkFlatLive M (tach M) ha 0 y).Rmat k from by
      funext y; rw [Cgen, dif_pos hk]]
    refine (DifferentiableAt.matMul ?_ (diffAt_chainQ _ _ u ?_)).add
      (DifferentiableAt.const_smul ?_ (1 : ℝ))
    · match k with
      | 0 => exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < 2
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Bmat (j + 1)) u
          simp only [genBlkFlatStruct, dif_pos hj]
          exact diffAt_bmatStack M (tach M) (j + 1) (ha.hdesc j hj) _ _ u
            (diffAt_readK M (tach M) ha ⟨j, hj⟩ u) (diffAt_readX M (tach M) ha ⟨j, hj⟩ u)
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Bmat (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
    · match k with
      | 0 => exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < 2
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Nblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_pos hj]; exact diffAt_readN M (tach M) ha ⟨j, hj⟩ u
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Nblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
    · match k with
      | 0 =>
        show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Rmat 0) u
        exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < 2
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Rmat (j + 1)) u
          simp only [genBlkFlatStruct, dif_pos hj]
          exact diffAt_rmatPad M (tach M) (j + 1) (ha.hdesc j hj) (ha.hub j) _ u
            (diffAt_readE M (tach M) ha ⟨j, hj⟩ u)
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Rmat (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
  · rw [show (fun y => Cgen (1 : ℝ) M (tach M)
          (genBlkFlatLive M (tach M) ha 0 y) (hleStruct M (tach M) ha) k)
        = fun y => (1 : ℝ) • (genBlkFlatLive M (tach M) ha 0 y).Rfin k from by
      funext y; rw [Cgen, dif_neg hk]]
    refine DifferentiableAt.const_smul ?_ (1 : ℝ)
    -- the leaf residual is the CONSTANT `0` (`rfin = 0`); `Rfin k = if k = 2 then 0 else 0 = 0`
    rw [show (fun y => (genBlkFlatLive M (tach M) ha 0 y).Rfin k) = fun _ => 0 from by
      funext y
      by_cases hkL : k = 2
      · subst hkL; simp only [genBlkFlatLive, dif_pos]
      · simp only [genBlkFlatLive, dif_neg hkL]]
    exact differentiableAt_const _

/-- The `genBlkFlatLive`-`0` decoder's `Agen` (radial `1`) is differentiable at each `s`. -/
theorem diffAt_Agen_E (ha : StructAdm M (tach M)) (u : Fin (routeMAmbient M) → ℝ) (s : ℕ) :
    DifferentiableAt ℝ
      (fun y => Agen (1 : ℝ) M (tach M)
        (genBlkFlatLive M (tach M) ha 0 y) (hleStruct M (tach M) ha) s) u := by
  by_cases hs : s < 2
  · rw [show (fun y => Agen (1 : ℝ) M (tach M)
          (genBlkFlatLive M (tach M) ha 0 y) (hleStruct M (tach M) ha) s)
        = fun y => chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s hs)
            ((genBlkFlatLive M (tach M) ha 0 y).Nblk s)
            ((genBlkFlatLive M (tach M) ha 0 y).Wblk s)
            (Cgen (1 : ℝ) M (tach M) (genBlkFlatLive M (tach M) ha 0 y)
              (hleStruct M (tach M) ha) (s + 1)) from by funext y; rw [Agen, dif_pos hs]]
    refine diffAt_chainA _ _ _ _ u ?_ ?_ (diffAt_Cgen_E ha u (s + 1))
    · match s with
      | 0 => exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < 2
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Nblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_pos hj]; exact diffAt_readN M (tach M) ha ⟨j, hj⟩ u
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Nblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
    · match s with
      | 0 => exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < 2
        · by_cases hj2 : j + 1 < 2
          · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Wblk (j + 1)) u
            simp only [genBlkFlatStruct, dif_pos hj, dif_pos hj2]
            exact diffAt_readW M (tach M) ha ⟨j, hj⟩ hj2 u
          · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Wblk (j + 1)) u
            simp only [genBlkFlatStruct, dif_pos hj, dif_neg hj2]; exact differentiableAt_const _
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Wblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
  · rw [show (fun y => Agen (1 : ℝ) M (tach M)
          (genBlkFlatLive M (tach M) ha 0 y) (hleStruct M (tach M) ha) s)
        = fun _ => 0 from by funext y; rw [Agen, dif_neg hs]]
    exact differentiableAt_const _

/-- **`BchartE` is differentiable** — the chain is polynomial in `y` (radial `1`, linear reads).
Mirrors `Bchart_differentiableAt`: reduce through the linear CLE `paramsEquivFlat`, the `Params` Pi,
and the per-component `reindex`, leaving the per-layer `diffAt_Agen_E`. -/
theorem BchartE_differentiableAt (ha : StructAdm M (tach M)) (u : Fin (routeMAmbient M) → ℝ) :
    DifferentiableAt ℝ (BchartE ha) u := by
  have hchart : DifferentiableAt ℝ (fun y => BparamsE ha y) u := by
    apply differentiableAt_pi.mpr
    intro s
    exact diffAt_reindex_finCongr _ _ _ u (diffAt_Agen_E ha u s.val)
  have hlin : DifferentiableAt ℝ (fun P => paramsEquivFlat M P) (BparamsE ha u) := by
    have hd := (paramsEquivFlatCLE M).differentiableAt (x := BparamsE ha u)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards with P; rw [paramsEquivFlatCLE_coe]
  exact hlin.comp u hchart

/-! ### The chart Jacobian abs-det = the single-axis monomial (gated on `|det DB| = 1`) -/

/-- **The chart Jacobian abs-det, gated on `|det DB| = 1`** — the pivot-generic radial wiring
`radialComp_abs_det_at` (`eBlockPivot ∈ activeM`, `activeM.card = minAdm`) gives
`|det Dφ| = |u eBlockPivot|^{minAdm−1} · |det DB|`; the `hBdet` gate collapses it to the single-axis
monomial. -/
theorem eDeepRank0_abs_det_of_hBdet (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (u : Fin (routeMAmbient M) → ℝ)
    (hBdet : |LinearMap.det (fderiv ℝ (BchartE ha)
        (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) u)).toLinearMap| = 1) :
    |LinearMap.det (fderiv ℝ (eDeepRank0Phi ha hr hc hp1 hp2) u).toLinearMap|
      = ∏ j, |u j| ^ (eDeepRank0_leafH ha hr hc j) := by
  set p₀ := eBlockPivot ha hr hc with hp₀
  have hasDB : HasFDerivAt (BchartE ha)
      (fderiv ℝ (BchartE ha) (pivotBlowupOn (activeM M ha) p₀ u))
      (pivotBlowupOn (activeM M ha) p₀ u) := (BchartE_differentiableAt ha _).hasFDerivAt
  rw [radialComp_abs_det_at M (activeM M ha) p₀ (eBlockPivot_mem_activeM ha hr hc) (activeM_card ha)
    (BchartE ha) (eDeepRank0Phi ha hr hc hp1 hp2) u _ (hmap_E ha hr hc hp1 hp2) hasDB, hBdet,
    mul_one]
  -- `|u p₀|^{minAdm−1} = ∏_j |u_j|^{leafH j}` (single-axis: `leafH p₀ = minAdm−1`, `0` else)
  rw [Finset.prod_eq_single p₀]
  · rw [eDeepRank0_leafH_pivot ha hr hc]
  · intro j _ hj; rw [eDeepRank0_leafH, if_neg hj, pow_zero]
  · intro h; exact absurd (Finset.mem_univ p₀) h

/-! ### `|det DB| = 1` — the Route B-shortcut (`BchartE = BchartLeaf` at `deepRank = 0`)

At `deepRank = 0` (`Text 2 = 0`) the leaf reader `rfinDirect ha y` is a `0×Wext 2` matrix, so it is the
zero matrix — equal to the `rfin = 0` of `BchartE`'s decoder. Hence `BchartE = BchartLeaf`, and the
banked `BchartLeaf_abs_det_free` gives `|det D(BchartLeaf) z| = |det (readK z ⟨0⟩)|^{r+c}`; at
`deepRank = 0` the K-core `readK z ⟨0⟩` is a `0×0` matrix, `det = 1`, so `1^{r+c} = 1`. -/

/-- At `deepRank = 0` (`Text 2 = 0`) the leaf reader is the zero matrix (`0×Wext 2`, no row index). -/
theorem rfinDirect_eq_zero_of_hdr0 (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (y : Fin (routeMAmbient M) → ℝ) :
    rfinDirect ha y = 0 := by
  ext i j
  exact absurd i.isLt (by omega)

/-- At `deepRank = 0`, `BchartE = BchartLeaf` (the two leaf residuals `0` and `rfinDirect` coincide). -/
theorem BchartE_eq_BchartLeaf_of_hdr0 (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0) :
    BchartE ha = BchartLeaf ha := by
  funext y
  rw [BchartE, BchartLeaf, BparamsE, BparamsLeaf, rfinDirect_eq_zero_of_hdr0 ha hdr0 y]

/-- At `deepRank = 0` the boundary-0 K-core `readK z ⟨0⟩` is the `0×0` empty matrix, so `det = 1`. -/
theorem readK0_det_one_of_hdr0 (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (z : Fin (routeMAmbient M) → ℝ) :
    (Matrix.of (readK M (tach M) ha z ⟨0, by decide⟩)).det = 1 := by
  have h2 : Text M (tach M) (0 + 2) = 0 := by rw [show (0 : ℕ) + 2 = 2 from rfl]; exact hdr0
  haveI hemp : IsEmpty (Fin (Text M (tach M) (0 + 2))) :=
    ⟨fun i => absurd i.isLt (by omega)⟩
  exact Matrix.det_isEmpty

/-- **`|det DB| = 1`** at `deepRank = 0` — via `BchartE = BchartLeaf` + the banked
`BchartLeaf_abs_det_free` + the empty-K determinant. -/
theorem BchartE_abs_det_eq_one (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (z : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (BchartE ha) z).toLinearMap| = 1 := by
  rw [BchartE_eq_BchartLeaf_of_hdr0 ha hdr0, BchartLeaf_abs_det_free ha z (eihd_hreg ha),
    readK0_det_one_of_hdr0 ha hdr0 z, abs_one, one_pow]

/-- **The deepRank = 0 chart Jacobian abs-det (UNCONDITIONAL)** — the pure single-axis monomial
`∏_j |u_j|^{leafH j} = |u eBlockPivot|^{minAdm−1}` (NO K-product): `eDeepRank0_abs_det_of_hBdet` with
`|det DB| = 1` discharged by `BchartE_abs_det_eq_one` (Route B-shortcut, `deepRank = 0`). -/
theorem eDeepRank0_abs_det (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (eDeepRank0Phi ha hr hc hp1 hp2) u).toLinearMap|
      = ∏ j, |u j| ^ (eDeepRank0_leafH ha hr hc j) :=
  eDeepRank0_abs_det_of_hBdet ha hr hc hp1 hp2 u
    (BchartE_abs_det_eq_one ha hdr0 (pivotBlowupOn (activeM M ha) (eBlockPivot ha hr hc) u))

/-! ## Item 7 — injectivity (the cov's `hinj`)

At `deepRank = 0` the boundary-0 K-core is `0×0`, so `slotReadV0`'s K-det `= 1 ≠ 0` UNCONDITIONALLY;
hence the banked V0/V1 recovery makes `BparamsLeaf` (`= BparamsE`) GLOBALLY injective, and the map
factors as `eDeepRank0Phi = BchartE ∘ pbo` with `pbo` injective off the pivot-zero plane. -/

/-- **The injectivity domain** — `{u | u eBlockPivot ≠ 0 ∧ ∀ j ∈ univ, u j ≠ 0}` (all coords nonzero),
matching the cov's `E = univ`. -/
def eDeepRank0InjDom (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    Set (Fin (routeMAmbient M) → ℝ) :=
  {u | u (eBlockPivot ha hr hc) ≠ 0 ∧ ∀ j ∈ (Finset.univ : Finset (Fin (routeMAmbient M))), u j ≠ 0}

/-- At `deepRank = 0` the boundary-0 K-core `readK z ⟨0⟩` has `det = 1 ≠ 0` UNCONDITIONALLY (`0×0`). -/
theorem slotReadV0_K_det_ne_zero_of_hdr0 (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (z : Fin (routeMAmbient M) → ℝ) :
    (slotReadV0 ha z).1.det ≠ 0 := by
  show (Matrix.of (readK M (tach M) ha z ⟨0, by decide⟩)).det ≠ 0
  rw [readK0_det_one_of_hdr0 ha hdr0 z]; exact one_ne_zero

/-- **`BchartE` is globally injective at `deepRank = 0`** — via `BchartE = BchartLeaf` + the banked V0/V1
recovery (unconditional K-det `= 1`). -/
theorem BchartE_injective_of_hdr0 (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0) :
    Function.Injective (BchartE ha) := by
  rw [BchartE_eq_BchartLeaf_of_hdr0 ha hdr0]
  intro y y' heq
  have heqP : BparamsLeaf ha y = BparamsLeaf ha y' :=
    (paramsEquivFlat M).injective
      (heq : paramsEquivFlat M (BparamsLeaf ha y) = paramsEquivFlat M (BparamsLeaf ha y'))
  have h0 : BparamsLeaf ha y 0 = BparamsLeaf ha y' 0 := congrFun heqP 0
  have h1 : BparamsLeaf ha y 1 = BparamsLeaf ha y' 1 := congrFun heqP 1
  have hK : (slotReadV0 ha y).1.det ≠ 0 := slotReadV0_K_det_ne_zero_of_hdr0 ha hdr0 y
  have hV0 : slotReadV0 ha y = slotReadV0 ha y' := slotReadV0_eq_of_BparamsLeaf0_eq ha hK h0
  have hN : Nfun ha y = Nfun ha y' := by rw [Nfun_eq_slotReadV0, Nfun_eq_slotReadV0, hV0]
  obtain ⟨hW, hLeaf⟩ := Wfun_Lfun_eq_of_BparamsLeaf1_eq ha hN h1
  refine (eIn ha).injective ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [eIn_projV0, eIn_projV0, hV0]
  · rw [← dWdC_eq_eInV1, ← dWdC_eq_eInV1]
    refine Prod.ext ?_ ?_
    · change (matrixReaderCLM (fun i j => readW0_idx ha i j)) y
        = (matrixReaderCLM (fun i j => readW0_idx ha i j)) y'
      simpa [matrixReaderCLM] using (hW : Wfun ha y = Wfun ha y')
    · change (matrixReaderCLM (fun i j => leaf_idx ha i j)) y
        = (matrixReaderCLM (fun i j => leaf_idx ha i j)) y'
      simpa [matrixReaderCLM] using (hLeaf : Lfun ha y = Lfun ha y')
  · rfl

/-- **injOn** — `eDeepRank0Phi` injective on `eDeepRank0InjDom` (the cov's `hinj`). Factor
`eDeepRank0Phi = BchartE ∘ pbo` (`hmap_E`); `pbo` injective off `{u_p = 0}` (banked, the domain
excludes it); `BchartE` globally injective (`BchartE_injective_of_hdr0`). -/
theorem eDeepRank0_injOn (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1) :
    Set.InjOn (eDeepRank0Phi ha hr hc hp1 hp2) (eDeepRank0InjDom ha hr hc) := by
  set p₀ := eBlockPivot ha hr hc with hp₀
  rw [hmap_E ha hr hc hp1 hp2]
  have hpbo_inj : Set.InjOn (pivotBlowupOn (activeM M ha) p₀) (eDeepRank0InjDom ha hr hc) := by
    have hsub : eDeepRank0InjDom ha hr hc
        ⊆ eDeepRank0InjDom ha hr hc \ {x | x p₀ = 0} := fun u hu => ⟨hu, hu.1⟩
    exact (pivotBlowupOn_injOn (activeM M ha) p₀ _).mono hsub
  exact (BchartE_injective_of_hdr0 ha hdr0).injOn.comp hpbo_inj (Set.mapsTo_image _ _)

end DLNFibre.DLN.RLCT
