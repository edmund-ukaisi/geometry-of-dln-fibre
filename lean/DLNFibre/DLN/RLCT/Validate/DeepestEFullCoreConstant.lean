import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

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

end DLNFibre.DLN.RLCT
