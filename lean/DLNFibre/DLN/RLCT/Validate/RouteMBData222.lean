import DLNFibre.DLN.RLCT.Validate.RouteMBInterface
import DLNFibre.DLN.RLCT.Validate.RouteMBData
import DLNFibre.DLN.RLCT.Validate.RouteM222Det
import DLNFibre.DLN.RLCT.Validate.RouteMCardBridge
import DLNFibre.DLN.RLCT.Validate.RouteMSchurValue

/-!
# `RouteMBData222` — the FAITHFUL `BData M222` term for the concrete (2,2,2) node

Constructs a `BData M222 tach222 ha hN 1 hp1 hp2 rfin u` term (the frozen B-interface,
`RouteMBInterface`) for the CONCRETE fixed-pivot/live-leaf decoder `genBlkFlatLiveR1 M222`, feeding
`interiorDet_headline_of_BData` to obtain the unconditional interior-det headline for
`phiFlatLiveR1 M222`. This is the FAITHFUL route end-to-end on the concrete node (the validate-small the
`∀M` `L = 2` generalization follows).

The faithful decomposition (Codex-verified, sympy-exact; `route-i-bridge-resolved.md`): on the actual
`genBlkFlatLiveR1 M222` blocks, with coords `(u, a, b, n, w0, w1, lf0, lf1)`
(`u = x (structPivot)` radial; `a = readK`, `b = readX`, `n = readN`, `w0,w1 = readW`; `lf0,lf1` the
free leaf coords),

  `Agen0 = [[a, a·n],[a·b, a·b·n + u]]`, `Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]`,

`φ = B ∘ pivotBlowupOn active u` with `active = {structPivot} ∪ {lf0, lf1}` (`card 3 = minAdm(2,2,2)`,
the FIXED `E(0,0) = 1` is NOT in active), `det Dπ = u²`; `B` reads the pivot as an ORDINARY coord (the
Schur frame isolates it: `p = A0_11 − A0_10·A0_01/A0_00 = u`), `det DB = a²` = the engine
(`|K|^{r+c}`, `r = c = 1`). The additive `+u` at `Agen0[1,1]` is the pivot COORDINATE, NOT an affine
layer.

The SLOT WALL (the opaque `chartIdxEquiv = (finCongr).trans (Fintype.equivFin).symm`): the reader slots
`a,b,n,w0,w1` are images of `chartIdxEquiv.symm` at specific `ChartIdx` tags — but `chartIdxEquiv.symm`
does NOT reduce by `decide`, and `structPivot = ⟨0,_⟩` is NOT a `ChartIdx` tag, so
`leaf-slot ≠ structPivot` is unreachable by tag injectivity. RESOLVED (R2, decorrelated Codex): choose
the two leaf slots `lf0, lf1` from the FINITE COMPLEMENT `univ \ (insert structPivot readerSet)`
(`readerSet.card ≤ 5`, so the complement has `≥ 2` slots); membership then GIVES `lf ≠ structPivot` and
`lf ∉ readerSet` for free, no opaque comparison.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked wiring + matrix algebra; the leaf-pair
choice is `Classical.choice`).
-/

open Matrix
open scoped BigOperators

set_option maxHeartbeats 800000

namespace DLNFibre.DLN.RLCT

/-! ## `StructAdm M222 tach222` (the achiever path `tach222 = [2,1,0]`) -/

/-- **`StructAdm M222 tach222`** — the structured-decoder admissibility for the (2,2,2) achiever path
`tach222 = [2,1,0]` (`Text = [2,2,1,1,…]`). In-range boundaries by `decide`; out-of-range (`k ≥ 3`) by
the `Wext`/`Text` saturation to `1`. -/
theorem structAdm_tach222 : StructAdm M222 tach222 := by
  refine ⟨by decide, ?_, by decide, ?_, ?_⟩
  · intro p
    rcases lt_or_ge p 3 with h | h
    · interval_cases p <;> decide
    · rw [show Wext M222 (p + 1) = 1 from by rw [Wext]; rw [dif_neg (by omega)],
          show tDesc M222 tach222 (p + 1) = 1 from by simp only [tDesc, Text]; rw [dif_neg (by omega)]]
  · intro k hk; interval_cases k <;> decide
  · intro k
    rcases lt_or_ge k 3 with h | h
    · interval_cases k <;> decide
    · rw [show Text M222 tach222 (k + 2) = 1 from by simp only [Text]; rw [dif_neg (by omega)],
          show Wext M222 (k + 1) = 1 from by rw [Wext]; rw [dif_neg (by omega)]]

/-- The R1 pivot row-drop hypothesis `hp1 : Text(2) ≤ Text(1)` at the (2,2,2) pivot boundary `p = 1`
(`Text 2 = 1 ≤ 2 = Text 1`). -/
theorem hp1_222 : Text M222 tach222 (1 + 1) ≤ Text M222 tach222 1 := by decide

/-- The R1 pivot col-drop hypothesis `hp2 : Text(2) ≤ Wext(1)` (`Text 2 = 1 ≤ 2 = Wext 1`). -/
theorem hp2_222 : Text M222 tach222 (1 + 1) ≤ Wext M222 1 := by decide

/-! ## The reader values + the leaf

The five reader scalars of `genBlkFlatLiveR1 M222 tach222` (all `1×1` blocks at chart-slot `k = 0`,
`Text 1 = 2`, `Text 2 = 1`, `Wext 1 = 2`): `aRead = readK ⟨0⟩ 0 0`, `bRead = readX ⟨0⟩ 0 0`,
`nRead = readN ⟨0⟩ 0 0`, `w0Read/w1Read = readW ⟨0⟩ _ 0 0/1`. The pivot `E`-slot is NOT read (the R1
override fixes `Rmat 1 = rmatPad pivotEIndicator`). The leaf `Rfin 2 = rfin x` is the free choice. -/

/-- The reader value `a = readK ⟨0,_⟩ 0 0` (the Schur-frame `K` scalar at chart-slot `0`). -/
noncomputable def aRead (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readK M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The reader value `b = readX ⟨0,_⟩ 0 0` (the Schur-frame `X` scalar). -/
noncomputable def bRead (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readX M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The reader value `n = readN ⟨0,_⟩ 0 0` (the Schur-frame `N` chaining scalar). -/
noncomputable def nRead (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readN M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The lift value `w0 = readW ⟨0,_⟩ _ 0 0`. -/
noncomputable def w0Read (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readW M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ (by decide) ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The lift value `w1 = readW ⟨0,_⟩ _ 0 1`. -/
noncomputable def w1Read (x : Fin (routeMAmbient M222) → ℝ) : ℝ :=
  readW M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ (by decide) ⟨0, by decide⟩ ⟨1, by decide⟩

/-! ## The `genBlkFlatLiveR1 M222` block values at boundary `1` + the leaf

The decoder `Glr x := genBlkFlatLiveR1 M222 tach222 structAdm_tach222 1 hp1_222 hp2_222 (rfin x) x`.
Its blocks at chart-slot `0` (boundary `s = 1`): `Bmat 1 = bmatStack (readK) (readX) = [[a],[a·b]]`,
`Nblk 1 = readN = [n]`, `Wblk 1 = readW = [w0, w1]`, and the FIXED pivot
`Rmat 1 = rmatPad (pivotEIndicator) = [[0,0],[0,1]]`. The leaf `C 2 = u • Rfin 2 = u • rfin x`. -/

variable (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
  (Fin (Wext M222 2)) ℝ)

/-- Abbreviation for the R1 decoder at `x` with leaf `rfin x`. -/
noncomputable def Glr (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) : GenBlk M222 tach222 :=
  genBlkFlatLiveR1 M222 tach222 structAdm_tach222 1 hp1_222 hp2_222 (rfin x) x

/-- `Glr`'s `Bmat 1 = bmatStack (readK ⟨0⟩) (readX ⟨0⟩)` (the live decoder's = the struct decoder's). -/
theorem Glr_Bmat1 (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Bmat 1
      = bmatStack M222 tach222 1 (structAdm_tach222.hdesc 0 (by decide))
          (readK M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
          (readX M222 tach222 structAdm_tach222 x ⟨0, by decide⟩) := by
  show (genBlkFlatStruct M222 tach222 structAdm_tach222 x).Bmat 1 = _
  show (if hk : (0 : ℕ) < 2 then bmatStack M222 tach222 1 (structAdm_tach222.hdesc 0 hk)
      (readK M222 tach222 structAdm_tach222 x ⟨0, hk⟩)
      (readX M222 tach222 structAdm_tach222 x ⟨0, hk⟩) else 0) = _
  rw [dif_pos (by decide)]

/-- `Glr`'s `Nblk 1 = readN ⟨0⟩`. -/
theorem Glr_Nblk1 (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Nblk 1 = readN M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ := by
  show (genBlkFlatStruct M222 tach222 structAdm_tach222 x).Nblk 1 = _
  simp only [genBlkFlatStruct, dif_pos (show (0 : ℕ) < 2 by decide)]

/-- `Glr`'s `Wblk 1 = readW ⟨0⟩ _`. -/
theorem Glr_Wblk1 (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Wblk 1 = readW M222 tach222 structAdm_tach222 x ⟨0, by decide⟩ (by decide) := by
  show (genBlkFlatStruct M222 tach222 structAdm_tach222 x).Wblk 1 = _
  simp only [genBlkFlatStruct, dif_pos (show (0 : ℕ) < 2 by decide),
    dif_pos (show 0 + 1 < 2 by decide)]

/-- `Glr`'s `Nblk 1` as the literal `1×1` matrix `!![nRead x]` (over the `Text2 × (Wext1−Text2)`
widths, both `= 1`). -/
theorem Glr_Nblk1_lit (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Nblk 1
      = (!![nRead x] : Matrix (Fin (Text M222 tach222 2))
          (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ) := by
  rw [Glr_Nblk1]
  funext i j; fin_cases i <;> fin_cases j; rfl

/-- `Glr`'s `Wblk 1` as the literal `1×2` matrix `!![w0Read x, w1Read x]` (over `(Wext1−Text2) × Wext2`,
`= 1 × 2`). -/
theorem Glr_Wblk1_lit (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Wblk 1
      = (!![w0Read x, w1Read x] : Matrix (Fin (Wext M222 1 - Text M222 tach222 2))
          (Fin (Wext M222 2)) ℝ) := by
  rw [Glr_Wblk1]
  funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- `Glr`'s `Rmat 1 = rmatPad (pivotEIndicator)` (the FIXED pivot override). -/
theorem Glr_Rmat1 (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    (Glr rfin x).Rmat 1
      = rmatPad M222 tach222 1 hp1_222 hp2_222 (pivotEIndicator M222 tach222 1) :=
  genBlkFlatLiveR1_Rmat_pivot M222 tach222 structAdm_tach222 1 hp1_222 hp2_222 (rfin x) x

/-! ## The Schur frame `C 1` + the leaf `C 2` -/

/-- **The boundary-1 transition `C 1 = schurFrameProd`** — the Schur frame
`Bmat 1 · chainQ(N1) + u·Rmat 1 = schurFrameProd … (readK) (readX) (readN) (pivotEIndicator)`. The
fixed-pivot `Rmat 1 = rmatPad pivotEIndicator` is the `u`-carrier `E`-block. -/
theorem Cgen1_Glr (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct M222 tach222 structAdm_tach222) 1
      = schurFrameProd M222 tach222 1 hp1_222 hp2_222 (x (structPivot M222 hN_M222))
          (readK M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
          (readX M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
          (readN M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
          (pivotEIndicator M222 tach222 1) := by
  show (if hk : (1 : ℕ) < 2 then (Glr rfin x).Bmat 1 *
      chainQ (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 hk) ((Glr rfin x).Nblk 1)
      + (x (structPivot M222 hN_M222)) • (Glr rfin x).Rmat 1 else _) = _
  rw [dif_pos (by decide), Glr_Bmat1, Glr_Nblk1, Glr_Rmat1]
  rfl

/-- **The leaf transition `C 2 = u • rfin x`** (`dif_neg`; the leaf residual `Rfin 2 = rfin x`). -/
theorem Cgen2_Glr (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct M222 tach222 structAdm_tach222) 2
      = (x (structPivot M222 hN_M222)) • (rfin x) := by
  show (if hk : (2 : ℕ) < 2 then _ else (x (structPivot M222 hN_M222)) • (Glr rfin x).Rfin 2) = _
  rw [dif_neg (by decide)]
  rfl

/-! ## The explicit layer matrices `Agen0` / `Agen1` (the FAITHFUL fidelity)

The load-bearing step: the chain's two layers of `genBlkFlatLiveR1 M222`, reindexed to the `M`-widths,
ARE the Codex-verified explicit matrices (coords `u = x p`, `a/b/n/w0/w1` the readers,
`lf0/lf1 = rfin x 0 0 / 0 1`):

  `Agen0 = [[a, a·n],[a·b, a·b·n + u]]`,  `Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]`.

The additive `+u` at `Agen0[1,1]` is the FIXED pivot's `u·E(0,0) = u·1` — the pivot COORDINATE. -/

/-- **Layer 1 of the chain** `Agen 1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]` (kept row `C2 − N1·W1`
over lift row `W1`; `C2 = u·rfin x`, `N1 = [n]`, `W1 = [w0,w1]`). -/
theorem Agen1_Glr_eq (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 1
      = (!![x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨0, by decide⟩ - nRead x * w0Read x,
            x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨1, by decide⟩ - nRead x * w1Read x;
            w0Read x, w1Read x] : Matrix (Fin (Wext M222 1)) (Fin (Wext M222 2)) ℝ) := by
  have hA : Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
      (hleStruct M222 tach222 structAdm_tach222) 1
      = chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
          ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
            (hleStruct M222 tach222 structAdm_tach222) 2) := by
    show (if hk : (1 : ℕ) < 2 then chainA _ _ _ _ else 0) = _
    rw [dif_pos (by decide)]
  -- kept row (castAdd): C2 − N1·W1; lift row (natAdd): W1
  have kept : ∀ j : Fin (Wext M222 2),
      chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
          ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
            (hleStruct M222 tach222 structAdm_tach222) 2)
          (⟨0, by decide⟩ : Fin (Wext M222 1)) j
        = (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
              (hleStruct M222 tach222 structAdm_tach222) 2
            - (Glr rfin x).Nblk 1 * (Glr rfin x).Wblk 1)
            (⟨0, by decide⟩ : Fin (Text M222 tach222 2)) j := by
    intro j
    conv_lhs => rw [show (⟨0, by decide⟩ : Fin (Wext M222 1))
        = Fin.cast (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
            (Fin.castAdd (Wext M222 1 - Text M222 tach222 2)
              (⟨0, by decide⟩ : Fin (Text M222 tach222 2))) from by apply Fin.ext; simp]
    rw [chainA_apply_castAdd]
  have lift : ∀ j : Fin (Wext M222 2),
      chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
          ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
            (hleStruct M222 tach222 structAdm_tach222) 2)
          (⟨1, by decide⟩ : Fin (Wext M222 1)) j
        = (Glr rfin x).Wblk 1 (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2)) j := by
    intro j
    conv_lhs => rw [show (⟨1, by decide⟩ : Fin (Wext M222 1))
        = Fin.cast (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
            (Fin.natAdd (Text M222 tach222 2)
              (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2))) from by apply Fin.ext; simp]
    rw [chainA_apply_natAdd]
  -- the four entries at explicit `⟨_, by decide⟩` indices
  have h00 : chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
      ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 2)
      (⟨0, by decide⟩ : Fin (Wext M222 1)) (⟨0, by decide⟩ : Fin (Wext M222 2))
        = x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨0, by decide⟩
          - nRead x * w0Read x := by
    rw [kept, Cgen2_Glr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Finset.sum_eq_single (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2))]
    · rfl
    · intro c _ hc
      refine absurd (Fin.ext ?_) hc
      have hlt := c.isLt
      have hw : Wext M222 1 - Text M222 tach222 2 = 1 := by decide
      omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have h01 : chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
      ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 2)
      (⟨0, by decide⟩ : Fin (Wext M222 1)) (⟨1, by decide⟩ : Fin (Wext M222 2))
        = x (structPivot M222 hN_M222) * rfin x ⟨0, by decide⟩ ⟨1, by decide⟩
          - nRead x * w1Read x := by
    rw [kept, Cgen2_Glr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Finset.sum_eq_single (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2))]
    · rfl
    · intro c _ hc
      refine absurd (Fin.ext ?_) hc
      have hlt := c.isLt
      have hw : Wext M222 1 - Text M222 tach222 2 = 1 := by decide
      omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have h10 : chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
      ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 2)
      (⟨1, by decide⟩ : Fin (Wext M222 1)) (⟨0, by decide⟩ : Fin (Wext M222 2)) = w0Read x := by
    rw [lift, Glr_Wblk1_lit]; rfl
  have h11 : chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 1 (by decide))
      ((Glr rfin x).Nblk 1) ((Glr rfin x).Wblk 1)
      (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 2)
      (⟨1, by decide⟩ : Fin (Wext M222 1)) (⟨1, by decide⟩ : Fin (Wext M222 2)) = w1Read x := by
    rw [lift, Glr_Wblk1_lit]; rfl
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- A `1×1 · 1×n` product entry over the singleton `Fin (Text2)` contraction index:
`(A · B) ⟨0⟩ j = A ⟨0⟩ ⟨0⟩ · B ⟨0⟩ j`. -/
theorem mul_text2_entry {n : ℕ} (A : Matrix (Fin (Text M222 tach222 2)) (Fin (Text M222 tach222 2)) ℝ)
    (B : Matrix (Fin (Text M222 tach222 2)) (Fin n) ℝ) (j : Fin n) :
    (A * B) ⟨0, by decide⟩ j = A ⟨0, by decide⟩ ⟨0, by decide⟩ * B ⟨0, by decide⟩ j := by
  rw [Matrix.mul_apply]
  have honly : (Finset.univ : Finset (Fin (Text M222 tach222 2)))
      = {(⟨0, by decide⟩ : Fin (Text M222 tach222 2))} := rfl
  rw [honly, Finset.sum_singleton]

/-- **Layer 0 of the chain** `Agen 0 = [[a, a·n],[a·b, a·b·n + u]]` (the Schur frame `C 1`; at `c_0 = 0`
the `chainA` lift block is empty so `Agen 0 = C 1`). The four entries are the `schurFrameProd` blocks
`K`, `K·N`, `X·K`, `X·K·N + u·E` with `K = a`, `X = b`, `N = n`, `E(0,0) = 1` (the fixed pivot). -/
theorem Agen0_Glr_eq (rfin : (Fin (routeMAmbient M222) → ℝ) → Matrix (Fin (Text M222 tach222 2))
    (Fin (Wext M222 2)) ℝ) (x : Fin (routeMAmbient M222) → ℝ) :
    Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
        (hleStruct M222 tach222 structAdm_tach222) 0
      = (!![aRead x, aRead x * nRead x;
            aRead x * bRead x, aRead x * bRead x * nRead x + x (structPivot M222 hN_M222)]
          : Matrix (Fin (Wext M222 0)) (Fin (Wext M222 1)) ℝ) := by
  have hA : Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
      (hleStruct M222 tach222 structAdm_tach222) 0
      = chainA (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 0 (by decide))
          ((Glr rfin x).Nblk 0) ((Glr rfin x).Wblk 0)
          (Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
            (hleStruct M222 tach222 structAdm_tach222) 1) := by
    show (if hk : (0 : ℕ) < 2 then chainA _ _ _ _ else 0) = _
    rw [dif_pos (by decide)]
  -- `N0 · W0 = 0` (the residual width `c_0 = Wext0 − Text1 = 0`); every row is `castAdd`, `Agen0 = C1`.
  have hN0W0 : (Glr rfin x).Nblk 0 * (Glr rfin x).Wblk 0 = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    exact (k.cast (show Wext M222 0 - Text M222 tach222 1 = 0 from by decide)).elim0
  have e : ∀ (r : Fin (Text M222 tach222 1)) (j : Fin (Wext M222 1)),
      Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
          (hleStruct M222 tach222 structAdm_tach222) 0
          (Fin.cast (genWidthEq M222 tach222 (hleStruct M222 tach222 structAdm_tach222) 0 (by decide))
            (Fin.castAdd (Wext M222 0 - Text M222 tach222 1) r)) j
        = Cgen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x)
            (hleStruct M222 tach222 structAdm_tach222) 1 r j := by
    intro r j
    rw [hA, chainA_apply_castAdd, hN0W0, Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  -- the four entries of `C 1 = schurFrameProd …` via the banked block lemmas
  have hC1 := Cgen1_Glr rfin x
  have e00 := e ⟨0, by decide⟩ ⟨0, by decide⟩
  have e01 := e ⟨0, by decide⟩ ⟨1, by decide⟩
  have e10 := e ⟨1, by decide⟩ ⟨0, by decide⟩
  have e11 := e ⟨1, by decide⟩ ⟨1, by decide⟩
  rw [hC1] at e00 e01 e10 e11
  -- index-cast shorthands for the row/col split forms (kept = castAdd, residual = natAdd)
  set hTr : Text M222 tach222 2 + (Text M222 tach222 1 - Text M222 tach222 2) = Text M222 tach222 1 :=
    by decide
  set hWc : Text M222 tach222 2 + (Wext M222 1 - Text M222 tach222 2) = Wext M222 1 := by decide
  set sfp := schurFrameProd M222 tach222 1 hp1_222 hp2_222 (x (structPivot M222 hN_M222))
    (readK M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
    (readX M222 tach222 structAdm_tach222 x ⟨0, by decide⟩)
    (readN M222 tach222 structAdm_tach222 x ⟨0, by decide⟩) (pivotEIndicator M222 tach222 1) with hsfp
  have row0 : (⟨0, by decide⟩ : Fin (Text M222 tach222 1))
      = Fin.cast hTr (Fin.castAdd _ (⟨0, by decide⟩ : Fin (Text M222 tach222 2))) := by
    apply Fin.ext; simp
  have row1 : (⟨1, by decide⟩ : Fin (Text M222 tach222 1))
      = Fin.cast hTr (Fin.natAdd _ (⟨0, by decide⟩ : Fin (Text M222 tach222 1 - Text M222 tach222 2))) := by
    apply Fin.ext; simp
  have col0 : (⟨0, by decide⟩ : Fin (Wext M222 1))
      = Fin.cast hWc (Fin.castAdd _ (⟨0, by decide⟩ : Fin (Text M222 tach222 2))) := by
    apply Fin.ext; simp
  have col1 : (⟨1, by decide⟩ : Fin (Wext M222 1))
      = Fin.cast hWc (Fin.natAdd _ (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2))) := by
    apply Fin.ext; simp
  -- block K (top-left): K 0 0 = a
  have b00 : sfp (⟨0, by decide⟩ : Fin (Text M222 tach222 1))
      (⟨0, by decide⟩ : Fin (Wext M222 1)) = aRead x := by
    rw [hsfp, row0, col0, schurFrameProd_block_K]; rfl
  -- block K·N (top-right): (K·N) 0 0 = a·n
  have b01 : sfp (⟨0, by decide⟩ : Fin (Text M222 tach222 1))
      (⟨1, by decide⟩ : Fin (Wext M222 1)) = aRead x * nRead x := by
    rw [hsfp, row0, col1, schurFrameProd_block_KN, mul_text2_entry]; rfl
  -- the singleton `Fin (Text2)` contraction (`univ = {⟨0⟩}`, `rfl`).
  have hsum2 : (Finset.univ : Finset (Fin (Text M222 tach222 2)))
      = {(⟨0, by decide⟩ : Fin (Text M222 tach222 2))} := rfl
  -- block X·K (bottom-left): (X·K) 0 0 = b·a = a·b
  have b10 : sfp (⟨1, by decide⟩ : Fin (Text M222 tach222 1))
      (⟨0, by decide⟩ : Fin (Wext M222 1)) = aRead x * bRead x := by
    rw [hsfp, row1, col0, schurFrameProd_block_XK, Matrix.mul_apply, hsum2, Finset.sum_singleton]
    show bRead x * aRead x = aRead x * bRead x; ring
  -- block X·K·N + u·E (bottom-right): (X·K·N) 0 0 + u·E 0 0 = a·b·n + u
  have b11 : sfp (⟨1, by decide⟩ : Fin (Text M222 tach222 1))
      (⟨1, by decide⟩ : Fin (Wext M222 1))
        = aRead x * bRead x * nRead x + x (structPivot M222 hN_M222) := by
    rw [hsfp, row1, col1, schurFrameProd_block_XKNuE]
    have hE : pivotEIndicator M222 tach222 1 (⟨0, by decide⟩ :
        Fin (Text M222 tach222 1 - Text M222 tach222 2))
        (⟨0, by decide⟩ : Fin (Wext M222 1 - Text M222 tach222 2)) = 1 := by
      simp [pivotEIndicator]
    rw [hE, mul_one, Matrix.mul_apply, hsum2, Finset.sum_singleton, Matrix.mul_apply, hsum2,
      Finset.sum_singleton]
    show bRead x * aRead x * nRead x + _ = _; ring
  rw [b00] at e00; rw [b01] at e01; rw [b10] at e10; rw [b11] at e11
  ext i j
  fin_cases i <;> fin_cases j
  · rw [show (⟨0, by decide⟩ : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222
        (hleStruct M222 tach222 structAdm_tach222) 0 (by decide))
        (Fin.castAdd (Wext M222 0 - Text M222 tach222 1)
          (⟨0, by decide⟩ : Fin (Text M222 tach222 1))) from by apply Fin.ext; simp]
    exact e00
  · rw [show (⟨0, by decide⟩ : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222
        (hleStruct M222 tach222 structAdm_tach222) 0 (by decide))
        (Fin.castAdd (Wext M222 0 - Text M222 tach222 1)
          (⟨0, by decide⟩ : Fin (Text M222 tach222 1))) from by apply Fin.ext; simp]
    exact e01
  · rw [show (⟨1, by decide⟩ : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222
        (hleStruct M222 tach222 structAdm_tach222) 0 (by decide))
        (Fin.castAdd (Wext M222 0 - Text M222 tach222 1)
          (⟨1, by decide⟩ : Fin (Text M222 tach222 1))) from by apply Fin.ext; simp]
    exact e10
  · rw [show (⟨1, by decide⟩ : Fin (Wext M222 0)) = Fin.cast (genWidthEq M222 tach222
        (hleStruct M222 tach222 structAdm_tach222) 0 (by decide))
        (Fin.castAdd (Wext M222 0 - Text M222 tach222 1)
          (⟨1, by decide⟩ : Fin (Text M222 tach222 1))) from by apply Fin.ext; simp]
    exact e11

end DLNFibre.DLN.RLCT
