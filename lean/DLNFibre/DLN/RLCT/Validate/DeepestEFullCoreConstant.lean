import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestEFullCoreConstant` — the "value-fold atom" ∂E/∂core(0)=0

The L2 diffeo-bridge's `hTilde` (PIN-1, `deepest_regAbsorb_exists`) needs, for the CONJUGATED core
absorb, that `D(deepestEFull)(0)` annihilates the core direction (so `eTilde`'s reg-reg block stays the
PIN-1 invertible frame `F` despite the conjugated `coreAbsorb.symm`'s reg→core shear). The clean,
formalizable form is the **value-constant atom**: at the regular-and-spectator-zero slice, `deepestEFull`
is INDEPENDENT of the core slot —

    deepestEFull (0, c, 0) = deepestEFull (0, 0, 0)   (∀ c)

which gives `D(fun c => deepestEFull (0,c,0))(0) = 0` (a constant has zero derivative) ⟹
`D(deepestEFull)(0).comp coreInCLM = 0` ⟹ `D_E ∘ (core-shear) = 0`.

**Why it holds (the frame-identity read, no Taylor).** `deepestEFull q` reads the reg-residual `{11,12,21}`
blocks of `P = reindex(prod(framedParamsPivot q))`. At reg=spec=0 every gauge read `X/Y/Z = 0`, so the
core slot `c` enters ONLY each framed layer's `(2,2)`-block. At `L = 2` the two layers are both boundary:
the boundary-inner frame identities `Qf (firstLayer) = 1` and `Pf (lastLayer) = 1` (hQf0/hPfL) — together
with the endpoint triangularity (hPtri layer-0 block-lower, hQtri layer-1 block-upper) — send the core's
contribution entirely into the product's `(2,2)` block, leaving `{11,12,21}` core-FREE. So the reg-residual
is constant in `c`. (Verified sympy against the real boundary frames: `{11,12,21}` is literally `(1,0,0)`
independent of `c`.)
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **`deepestEFull` reads off the framed-product reg-blocks** (per-coordinate, the un-squared
`deepestEFull_sq_sum_eq_blocks`): two points whose framed reindexed products agree on the `{11,12,21}`
blocks have equal `deepestEFull`. (Each coordinate IS a block entry by the `deepestEFull` def, via
`regResidualPack`.) -/
theorem deepestEFull_eq_of_framedProd_regBlocks_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q₁ q₂ : DeepestSplit H r (deepestNGauge H r))
    (h11 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf q₁))).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H (framedParamsPivot H r hr hL J Pf Qf q₂))).toBlocks₁₁)
    (h12 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf q₁))).toBlocks₁₂
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H (framedParamsPivot H r hr hL J Pf Qf q₂))).toBlocks₁₂)
    (h21 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf q₁))).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H (framedParamsPivot H r hr hL J Pf Qf q₂))).toBlocks₂₁) :
    deepestEFull H r hr hL J Pf Qf q₁ = deepestEFull H r hr hL J Pf Qf q₂ := by
  funext i
  rcases hpack : regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    simp only [deepestEFull, hpack]
  · rw [h11]
  · rw [h12]
  · rw [h21]

/-! ## The boundary deepest-block vanishing (re-derived self-contained; cf. genm-l2psi's copies) -/

/-- `M̄Y_s = deepBlkY_s = 0` at **layer 0** (`L ≥ 2`): `toBlocks₁₂` reads cols `≥ r`, which vanish. -/
theorem deepBlkY_layer0_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (s : Fin L) (hs : (s : ℕ) = 0) :
    deepBlkY H r B hB hr hL s = 0 := by
  funext i j
  change (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inl i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inr j)) = 0
  rw [rThresholdSplit_symm_inr]
  exact deepestPoint_layer0_cols_vanish H r B hB hr hL s hL2 hs _ _ (by simp)

/-- `M̄Z_s = deepBlkZ_s = 0` at **layer (L−1)** (`L ≥ 2`): `toBlocks₂₁` reads rows `≥ r`, which vanish. -/
theorem deepBlkZ_layerLast_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (s : Fin L) (hs : (s : ℕ) + 1 = L) :
    deepBlkZ H r B hB hr hL s = 0 := by
  funext i j
  change (deepestPoint H r B hB hr hL s)
      ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm (Sum.inr i))
      ((rThresholdSplit r (H s.succ) (hr s.succ)).symm (Sum.inl j)) = 0
  rw [rThresholdSplit_symm_inr]
  exact deepestPoint_layerLast_rows_vanish H r B hB hr hL s hL2 hs _ _ (by simp)

/-! ## The pure-`{22}` conjugation kernel (cast-free `fromBlocks` algebra)

The geometric heart of the atom's block-constancy, isolated as cast-free `fromBlocks_multiply` facts:
a pure-`{22}` block `fromBlocks 0 0 0 T`, left-multiplied by a block-LOWER `fromBlocks a 0 c d` and
right-multiplied by a block-UPPER `fromBlocks e f 0 g`, stays pure-`{22}` (`= fromBlocks 0 0 0 (d·T·g)`).
This is why the core (which sits in each framed layer's `{22}` at reg=spec=0) never reaches the framed
product's `{11,12,21}` — the boundary frames are block-lower (Pf_0, hPtri) / block-upper (Qf_1, hQtri),
and the boundary-inner ones are the identity (Qf_0, Pf_1). -/

/-- **The pure-`{22}` conjugation**: block-LOWER `P = fromBlocks a 0 c d` (rows/cols `r ⊕ m`) · pure-`{22}`
`fromBlocks 0 0 0 T` (`T : m × n`) · block-UPPER `Q = fromBlocks e f 0 g` (rows/cols `r ⊕ n`) = pure-`{22}`
`fromBlocks 0 0 0 (d·T·g)`. So the `{11,12,21}` blocks are `0` — INDEPENDENT of the core `T`. (Two
cast-free `fromBlocks_multiply` collapses: `P · pure = fromBlocks 0 0 0 (d·T)`, then `· Q = fromBlocks 0
0 0 (d·T·g)`.) -/
theorem blockLowerUpper_conj_pureT {r m n : Type*} [Fintype r] [Fintype m] [Fintype n]
    [DecidableEq r] [DecidableEq m] [DecidableEq n]
    (a : Matrix r r ℝ) (c : Matrix m r ℝ) (d : Matrix m m ℝ)
    (e : Matrix r r ℝ) (f : Matrix r n ℝ) (g : Matrix n n ℝ)
    (T : Matrix m n ℝ) :
    Matrix.fromBlocks a 0 c d
        * Matrix.fromBlocks (0 : Matrix r r ℝ) (0 : Matrix r n ℝ) (0 : Matrix m r ℝ) T
        * Matrix.fromBlocks e f 0 g
      = Matrix.fromBlocks 0 0 0 (d * T * g) := by
  have h1 : Matrix.fromBlocks a (0 : Matrix r m ℝ) c d
        * Matrix.fromBlocks (0 : Matrix r r ℝ) (0 : Matrix r n ℝ) (0 : Matrix m r ℝ) T
      = Matrix.fromBlocks (0 : Matrix r r ℝ) (0 : Matrix r n ℝ) (0 : Matrix m r ℝ) (d * T) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [h1, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc]

/-- **The block-corner product**: `fromBlocks 1 0 0 P · fromBlocks 1 0 0 Q = fromBlocks 1 0 0 (P·Q)`
(`fromBlocks_multiply` + matrix arithmetic). Cast-free over arbitrary middle dims — applied to the two
framed layers it collapses the reindexed product's `{11,12,21}` to `(1,0,0)` while sidestepping the
`Fin.succ 0` vs `Fin.castSucc 1` middle-index friction (the lemma's `n` defeq-unifies with both). -/
theorem fromBlocks_one_corner_mul {r m n p : Type*} [Fintype r] [Fintype m] [Fintype n]
    [DecidableEq r] [DecidableEq m] [DecidableEq n]
    (P : Matrix m n ℝ) (Q : Matrix n p ℝ) :
    Matrix.fromBlocks (1 : Matrix r r ℝ) 0 0 P * Matrix.fromBlocks (1 : Matrix r r ℝ) 0 0 Q
      = Matrix.fromBlocks 1 0 0 (P * Q) := by
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]

/-! ## Per-layer normalization: `reindex(framedLayer at zero reads) = fromBlocks 1 0 0 (junk)` -/

/-- **The reindexed framed layer at zero reads is `fromBlocks 1 0 0 (junk)`** (so its `{11,12,21}` blocks
are the corner blocks, INDEPENDENT of the core `T`), given `reindex P` block-lower (`hP12`) and
`reindex Q` block-upper (`hQ21`). At zero reads `framedLayer = Rsym(corner) + P·Rsym(fromBlocks 0 0 0
T)·Q`; the corner round-trips, and the core term lands in `{22}` via `blockLowerUpper_conj_pureT`. -/
theorem reindex_framedLayer_zeroReads_eq_corner (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : Fin L)
    (P : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (T : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)
    (hP12 : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) P).toBlocks₁₂ = 0)
    (hQ21 : (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) Q).toBlocks₂₁ = 0) :
    Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (framedLayer H r hr s P Q 0 0 0 T)
      = Matrix.fromBlocks 1 0 0
          ((Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
              (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) P).toBlocks₂₂
            * T
            * (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
              (rThresholdSplit r (H s.succ) (hr s.succ)) Q).toBlocks₂₂) := by
  set eC := rThresholdSplit r (H s.castSucc) (hr s.castSucc) with heC
  set eS := rThresholdSplit r (H s.succ) (hr s.succ) with heS
  -- `framedLayer` at zero reads = `Rsym(corner) + P·Rsym(fromBlocks 0 0 0 T)·Q`; reindex is additive.
  rw [framedLayer]
  rw [show Matrix.reindex eC eS
        (Matrix.reindex eC.symm eS.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
          + P * Matrix.reindex eC.symm eS.symm
              (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 T) * Q)
      = (Matrix.reindex eC.symm eS.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)).submatrix
          eC.symm eS.symm
        + (P * Matrix.reindex eC.symm eS.symm
              (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 T) * Q).submatrix eC.symm eS.symm from by
    rw [Matrix.reindex_apply]; rfl]
  -- The corner round-trips (Codex: `reindex e.symm e'.symm` then `.submatrix e.symm e'.symm`).
  have hcorner : (Matrix.reindex eC.symm eS.symm
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)).submatrix eC.symm eS.symm
      = Matrix.fromBlocks 1 0 0 0 := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_symm,
      Equiv.self_comp_symm, Matrix.submatrix_id_id]
  -- The frame term: push the read through the triple product, then the kernel lands it in {22}.
  have hsplit : (P * Matrix.reindex eC.symm eS.symm
        (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 T) * Q).submatrix eC.symm eS.symm
      = Matrix.reindex eC eC P
          * Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 T
          * Matrix.reindex eS eS Q := by
    have hP : P = (Matrix.reindex eC eC P).submatrix eC eC := by
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
        Matrix.submatrix_id_id]
    have hQ : Q = (Matrix.reindex eS eS Q).submatrix eS eS := by
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
        Matrix.submatrix_id_id]
    simp only [Matrix.reindex_apply, Equiv.symm_symm]
    conv_lhs => rw [hP, hQ]
    rw [Matrix.submatrix_mul_equiv (Matrix.reindex eC eC P)
        (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 T) eC eC eS,
      Matrix.submatrix_mul_equiv (Matrix.reindex eC eC P
        * Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 T) (Matrix.reindex eS eS Q) eC eS eS]
    simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id,
      Matrix.reindex_apply]
  -- Manufacture block-lower P / block-upper Q via `fromBlocks_toBlocks` + hP12/hQ21.
  have hPblk : Matrix.reindex eC eC P
      = Matrix.fromBlocks (Matrix.reindex eC eC P).toBlocks₁₁ (0 : Matrix (Fin r) (Fin (H s.castSucc - r)) ℝ)
          (Matrix.reindex eC eC P).toBlocks₂₁ (Matrix.reindex eC eC P).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eC eC P)]
    rw [hP12]
  have hQblk : Matrix.reindex eS eS Q
      = Matrix.fromBlocks (Matrix.reindex eS eS Q).toBlocks₁₁ (Matrix.reindex eS eS Q).toBlocks₁₂
          (0 : Matrix (Fin (H s.succ - r)) (Fin r) ℝ) (Matrix.reindex eS eS Q).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eS eS Q)]
    rw [hQ21]
  rw [hcorner, hsplit]
  rw [show (Matrix.reindex eC eC P) * Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 T
        * (Matrix.reindex eS eS Q)
      = Matrix.fromBlocks 0 0 0
          ((Matrix.reindex eC eC P).toBlocks₂₂ * T * (Matrix.reindex eS eS Q).toBlocks₂₂) from by
    conv_lhs => rw [hPblk, hQblk]
    rw [blockLowerUpper_conj_pureT (Matrix.reindex eC eC P).toBlocks₁₁
      (Matrix.reindex eC eC P).toBlocks₂₁ (Matrix.reindex eC eC P).toBlocks₂₂
      (Matrix.reindex eS eS Q).toBlocks₁₁ (Matrix.reindex eS eS Q).toBlocks₁₂
      (Matrix.reindex eS eS Q).toBlocks₂₂ T]]
  -- `fromBlocks 1 0 0 0 + fromBlocks 0 0 0 J = fromBlocks 1 0 0 J`.
  rw [Matrix.fromBlocks_add]
  simp only [add_zero, zero_add]

/-! ## `framedParamsPivot(0,c,0)` per-layer at zero reg/spec = `framedLayer ... 0 0 0 (core)` -/

/-- At reg=spec=0, a NON-last framed layer is `framedLayer s (Pf s)(Qf s) 0 0 0 (core read)` (reads
vanish). -/
theorem framedParamsPivot_zeroReg_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (c : Fin (flatDim (deepestM H r)) → ℝ) (s : Fin L) (hs : s ≠ lastLayer hL) :
    framedParamsPivot H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) s
      = framedLayer H r hr s (Pf s) (Qf s) 0 0 0 ((paramsEquivFlat (deepestM H r)).symm c s) := by
  rw [framedParamsPivot_of_ne_last H r hr hL J Pf Qf _ s hs]
  show framedLayer H r hr s (Pf s) (Qf s)
      (readX H r hr hL (((0 : Fin (deepestNReg H r) → ℝ), c,
        (0 : Fin (deepestNGauge H r) → ℝ)).1, (_, c, _).2.2) s) _ _ _
    = _
  rw [show (((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)).1,
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)).2.2)
      = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl,
    readX_zero H r hr hL s, readY_zero H r hr hL s, readZ_zero H r hr hL s]

/-- At reg=spec=0, the LAST framed layer (pivot col split) is `corner + Pf_last · pivotRsym(fromBlocks 0
0 0 (core read)) · Qf_last` (reads vanish; the pivot column split `pivotJSucc J`). -/
theorem framedParamsPivot_zeroReg_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (c : Fin (flatDim (deepestM H r)) → ℝ) :
    framedParamsPivot H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) (lastLayer hL)
      = Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
            (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
          + Pf (lastLayer hL)
            * Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
                (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
                (Matrix.fromBlocks 0 0 0
                  ((paramsEquivFlat (deepestM H r)).symm c (lastLayer hL)))
            * Qf (lastLayer hL) := by
  rw [framedParamsPivot_last H r hr hL J Pf Qf
    ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))]
  rw [show (((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)).1,
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)).2.2)
      = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) from rfl,
    readX_zero H r hr hL (lastLayer hL), readY_zero H r hr hL (lastLayer hL),
    readZ_zero H r hr hL (lastLayer hL)]

/-! ## The two-factor assembly: `reindex(prod(framedParamsPivot(0,c,0))) = fromBlocks 1 0 0 (junk)`

At `L = 2`, `prod(framedParamsPivot(0,c,0)) = layer0 · layer1`; each reindexes (the per-layer norm) to
`fromBlocks 1 0 0 T_s'`; `reindex_mul_fromBlocks` then gives the product reindexed to a `fromBlocks` whose
`{11,12,21}` are the corner blocks `(1,0,0)` — INDEPENDENT of the core `c`. The outer pivot-column split
collapses to the threshold split under `J = frontEmbed` (`hJfront'`). -/

/-- **The framed product at zero reg/spec reindexes to `fromBlocks 1 0 0 (junk)`** (so its `{11,12,21}`
blocks are the corner `(1,0,0)`, INDEPENDENT of the core `c`). The two-factor assembly, `L = 2`. -/
theorem prod_framedParamsPivot_zeroReg_eq_corner (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (c : Fin (flatDim (deepestM H r)) → ℝ) :
    ∃ junk : Matrix (Fin (H 0 - r)) (Fin (H (Fin.last 2) - r)) ℝ,
      Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J)
          (prod H (framedParamsPivot H r hr hL J Pf Qf
            ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))))
        = Matrix.fromBlocks 1 0 0 junk := by
  -- Index facts (Codex: `Fin.ext`, NOT `decide` on a prop with `lastLayer hL` free).
  have hlast1 : lastLayer hL = (1 : Fin 2) := by apply Fin.ext; simp only [lastLayer]; omega
  have h0ne : (0 : Fin 2) ≠ lastLayer hL := by rw [hlast1]; decide
  -- Collapse the outer pivot col split to the threshold split (`J = frontEmbed`).
  have hpivOuter : pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J
      = rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) := by
    rw [hJfront]; exact pivotThresholdSplit_frontEmbed H r hr
  have hpivLast : pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J)
      = rThresholdSplit r (H ((lastLayer hL).succ)) (hr _) := by
    rw [hJfront]; exact pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL
  -- Bridge each framed-pivot layer at zero reads to `framedLayer ... 0 0 0 (core)` (defeq for last
  -- after `hpivLast` collapses the pivot split to the threshold split).
  have hbridge0 : framedParamsPivot H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) (0 : Fin 2)
      = framedLayer H r hr 0 (Pf 0) (Qf 0) 0 0 0 ((paramsEquivFlat (deepestM H r)).symm c 0) :=
    framedParamsPivot_zeroReg_of_ne H r hr hL J Pf Qf c 0 h0ne
  have hbridge1 : framedParamsPivot H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) (lastLayer hL)
      = framedLayer H r hr (lastLayer hL) (Pf (lastLayer hL)) (Qf (lastLayer hL)) 0 0 0
          ((paramsEquivFlat (deepestM H r)).symm c (lastLayer hL)) := by
    rw [framedParamsPivot_zeroReg_last H r hr hL J Pf Qf c, hpivLast]; rfl
  -- The per-layer norm at each layer, then bridge the source into the assembly's index form via `show`.
  have hnorm0 := reindex_framedLayer_zeroReads_eq_corner H r hr 0 (Pf 0) (Qf 0)
    ((paramsEquivFlat (deepestM H r)).symm c 0) (hPtri 0) (hQtri 0)
  have hnorm1 := reindex_framedLayer_zeroReads_eq_corner H r hr (lastLayer hL) (Pf (lastLayer hL))
    (Qf (lastLayer hL)) ((paramsEquivFlat (deepestM H r)).symm c (lastLayer hL))
    (hPtri (lastLayer hL)) (hQtri (lastLayer hL))
  rw [← hbridge0] at hnorm0
  rw [← hbridge1] at hnorm1
  rw [hlast1] at hnorm1
  -- Assemble via `reindex_mul_split` (factor the reindexed product into the two reindexed layers, with the
  -- middle split `rThr (H 1)`), substitute each layer's per-layer norm `= fromBlocks 1 0 0 Jₛ` (hnorm0/1),
  -- then `fromBlocks_multiply` — which yields the block product with the CANONICAL `*` instance, so the
  -- `{11,12,21}` blocks reduce by `simp [zero_mul, mul_zero, one_mul, …]`. `{22}` is the witness.
  have hsplit := reindex_mul_split (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
      (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)))
      (framedParamsPivot H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) (0 : Fin 2))
      (framedParamsPivot H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) (1 : Fin 2))
  rw [show Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
        (framedParamsPivot H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) (0 : Fin 2))
      = _ from hnorm0,
    show Matrix.reindex (rThresholdSplit r (H 1) (hr 1))
          (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)))
        (framedParamsPivot H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) (1 : Fin 2))
      = _ from hnorm1] at hsplit
  -- Collapse the `fromBlocks · fromBlocks` by the corner-product helper via `.trans` (term application
  -- defeq-unifies the `Fin.succ 0` / `Fin.castSucc 1` middle; a syntactic `rw` cannot).
  have hmul := hsplit.trans (fromBlocks_one_corner_mul _ _)
  -- Name the whole reindexed product `M` (collapse the outer pivot split first). Witness = `M.toBlocks₂₂`;
  -- the {11,12,21} blocks come out `(1,0,0)`, read OFF `hmul` via `simpa … using congrArg toBlocksᵢⱼ hmul`
  -- (which carries `hmul`'s defeq through `congrArg`, sidestepping the `rw`-find + `*`-instance friction).
  rw [hpivOuter]
  set M : Matrix (Fin r ⊕ Fin (H 0 - r)) (Fin r ⊕ Fin (H (Fin.last 2) - r)) ℝ :=
    Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
      (rThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)))
      (prod H (framedParamsPivot H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)))) with hM
  change ∃ junk : Matrix (Fin (H 0 - r)) (Fin (H (Fin.last 2) - r)) ℝ,
    M = Matrix.fromBlocks 1 0 0 junk
  rw [prodDecode_eq_two_of_L2 H (framedParamsPivot H r hr hL J Pf Qf
    ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)))] at hM
  simp only [finCongr_refl, Matrix.reindex_refl_refl] at hM
  -- Each block fact: `(prod).toBlocksᵢⱼ` is DEFEQ to `(hmul.LHS).toBlocksᵢⱼ` (`hM ▸` + the product's `*`
  -- differs only by instance), so `(congrArg toBlocksᵢⱼ hmul).trans (toBlocks_fromBlocksᵢⱼ …)` matches the
  -- goal up to defeq (no syntactic `rw`). hmul's RHS is now `fromBlocks 1 0 0 (J0·J1)`, so the blocks are
  -- `(1,0,0)` by the corresponding `toBlocks_fromBlocks` rfl-lemma.
  have h11 : M.toBlocks₁₁ = (1 : Matrix (Fin r) (Fin r) ℝ) :=
    hM ▸ (congrArg Matrix.toBlocks₁₁ hmul).trans (Matrix.toBlocks_fromBlocks₁₁ _ _ _ _)
  have h12 : M.toBlocks₁₂ = (0 : Matrix (Fin r) (Fin (H (Fin.last 2) - r)) ℝ) :=
    hM ▸ (congrArg Matrix.toBlocks₁₂ hmul).trans (Matrix.toBlocks_fromBlocks₁₂ _ _ _ _)
  have h21 : M.toBlocks₂₁ = (0 : Matrix (Fin (H 0 - r)) (Fin r) ℝ) :=
    hM ▸ (congrArg Matrix.toBlocks₂₁ hmul).trans (Matrix.toBlocks_fromBlocks₂₁ _ _ _ _)
  refine ⟨M.toBlocks₂₂, ?_⟩
  calc
    M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
        (Matrix.fromBlocks_toBlocks M).symm
    _ = Matrix.fromBlocks 1 0 0 M.toBlocks₂₂ := by rw [h11, h12, h21]

/-! ## The atom: `deepestEFull` is constant in the core at the reg=spec=0 slice (`L = 2`) -/

/-- **The value-fold atom** (`L = 2`): at the regular-and-spectator-zero slice, `deepestEFull` is
INDEPENDENT of the core slot —

    deepestEFull (0, c, 0) = deepestEFull (0, 0, 0)   (∀ c)

so `D(fun c => deepestEFull (0,c,0))(0) = 0`. Proof: by `prod_framedParamsPivot_zeroReg_eq_corner`, the
reindexed framed product at `(0,c,0)` is `fromBlocks 1 0 0 (junk c)` — its `{11,12,21}` blocks are the
core-INDEPENDENT corner `(1,0,0)`. So both `(0,c,0)` and `(0,0,0)` have the SAME `{11,12,21}` blocks, and
`deepestEFull_eq_of_framedProd_regBlocks_eq` concludes equal `deepestEFull`. -/
theorem deepestEFull_coreConstant (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0)
    (c : Fin (flatDim (deepestM H r)) → ℝ) :
    deepestEFull H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))
      = deepestEFull H r hr hL J Pf Qf
        ((0 : Fin (deepestNReg H r) → ℝ),
          (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ)) := by
  -- The reindexed framed product is `fromBlocks 1 0 0 (junk)` at BOTH core values.
  obtain ⟨junkc, hjunkc⟩ :=
    prod_framedParamsPivot_zeroReg_eq_corner H r hr hL J hJfront Pf Qf hPtri hQtri c
  obtain ⟨junk0, hjunk0⟩ :=
    prod_framedParamsPivot_zeroReg_eq_corner H r hr hL J hJfront Pf Qf hPtri hQtri 0
  -- Apply the readback reduction; each `{11,12,21}` block of both equals the corner block (1,0,0).
  refine deepestEFull_eq_of_framedProd_regBlocks_eq H r hr hL J Pf Qf _ _ ?_ ?_ ?_
  · rw [hjunkc, hjunk0, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₁]
  · rw [hjunkc, hjunk0, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₁₂]
  · rw [hjunkc, hjunk0, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₁]

end DLNFibre.DLN.RLCT
