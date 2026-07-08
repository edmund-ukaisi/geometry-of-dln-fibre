import DLNFibre.DLN.RLCT.Validate.DeepestChainUnitGerm
import DLNFibre.DLN.RLCT.Validate.DeepestDeepBlkBoundaryGen
import DLNFibre.DLN.RLCT.Validate.FrontPivotProducer

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestHsub4coreInvGerm` — the DECODE-chain invertibility germs
(#120 `hstep2`, item 3, Piece 2)

The three eventual-`IsUnit` germs the general-`L` `hsub4core` keystone
`deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart` (`DeepestHsub4coreGen`) consumes as
its `hLayer` / `hPart` / `hMid11inv` hypotheses, over a neighbourhood of the basepoint
`x₀ = paramsEquivFlat (deepestPoint H r B)`. Unlike the `DeepestChainUnitGerm` bricks (for the
FRAMED chain `deepestChain (framedParamsPivot … (split x))`), these are for the **DECODE chain**
`deepestChain ((paramsEquivFlat H).symm x)` — the raw flat-parameter chain the telescope reads. They
are Producer-1-FREE: `(paramsEquivFlat H).symm` is a continuous linear equiv, so `x`-continuity is
immediate, and at the basepoint the decode chain is the `deepestPoint` chain.

## The basepoint values (all units)

At `x₀`, `(paramsEquivFlat H).symm x₀ = deepestPoint`, and:

* **`hLayer`** — `(deepestChain deepestPoint k).toBlocks₁₁ = deepBlkA k`
  (`deepestChain_toBlocks₁₁_eq_layer` + the `deepBlkA` def), a unit by `hDA`;
* **`hPart`** — `(partProd (deepestChain deepestPoint) k).toBlocks₁₁ = ∏_{j<k} deepBlkA j`
  (`partProd_deepestChain_deepestPoint_toBlocks₁₁_isUnit`, a `.toBlocks₁₂ = 0` induction:
  the non-last deepest layers have `deepBlkY = 0`), a product of units;
* **`hMid11inv`** — at `J = frontEmbed`, `pivotThresholdSplit J = rThresholdSplit`;
  `prod deepestPoint = B`, and `(reindex (rThr 0) (rThr last) B).toBlocks₁₁ =
  (partProd (deepestChain deepestPoint) L).toBlocks₁₁` (via `pivotFront_toBlocks₁₁_eq_chainCol` +
  `reindex_prod_eq_partProd`), the `k = L` case of `hPart`.

Determinant continuity + `ContinuousAt.eventually_ne` (`eventually_isUnit_of_continuousAt_det`) then
propagates each basepoint unit to a neighbourhood.
-/

open Matrix MeasureTheory Topology
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## The decode-chain layer / block bridges (`k < L`) -/

/-- **The decode-chain layer `(1,1)` block is the layer's threshold `(1,1)` block.** For `k < L` the
`deepestChain` `(1,1)` block reads the first `r` rows/cols, coinciding with the `rThresholdSplit`
`(1,1)` block of the raw layer `A ⟨k, hk⟩` (the `deepestChainSplit`/`finCongr` casts are
value-preserving on those indices). At `A = deepestPoint` the RHS is `deepBlkA k`. -/
theorem deepestChain_toBlocks₁₁_eq_layer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L) :
    (deepestChain H r hr A k).toBlocks₁₁
      = (Matrix.reindex (rThresholdSplit r (H (⟨k, hk⟩ : Fin L).castSucc) (hr _))
          (rThresholdSplit r (H (⟨k, hk⟩ : Fin L).succ) (hr _)) (A ⟨k, hk⟩)).toBlocks₁₁ := by
  funext i j
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    deepestChain, deepestChainLayer, dif_pos hk, deepestChainSplit, rThresholdSplit_symm_inl,
    finCongr_symm, finCongr_apply]
  congr 1

/-- **The decode-chain layer `(1,2)` block vanishes when the raw layer's columns `≥ r` vanish.** The
`deepestChain` `(1,2)` block reads columns `≥ r`, killed by the col-vanishing hypothesis. At
`A = deepestPoint` and a non-last layer this is `deepestPoint_layer0_cols_vanish` /
`deepestPoint_interior_cols_vanish`. -/
theorem deepestChain_toBlocks₁₂_eq_zero_of_cols_vanish (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (k : ℕ) (hk : k < L)
    (hcol : ∀ (i : Fin (H (⟨k, hk⟩ : Fin L).castSucc)) (j : Fin (H (⟨k, hk⟩ : Fin L).succ)),
      r ≤ (j : ℕ) → A ⟨k, hk⟩ i j = 0) :
    (deepestChain H r hr A k).toBlocks₁₂ = 0 := by
  funext i j
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    deepestChain, deepestChainLayer, dif_pos hk, deepestChainSplit, rThresholdSplit_symm_inl,
    rThresholdSplit_symm_inr, finCongr_symm, finCongr_apply, Matrix.zero_apply]
  apply hcol
  simp only [Fin.val_cast]
  omega

/-! ## The decode-chain layer / partProd continuity in the flat parameter -/

/-- Continuity of the whole decode-chain layer `A ↦ deepestChain H r hr A k` in the parameter tuple
`A`. For `k < L` it is a double reindex of the layer selection `A ↦ A ⟨k, hk⟩`; for `k ≥ L`
it is the constant corner default. -/
theorem continuous_deepestChain_layer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (k : ℕ) :
    Continuous (fun A : Params H => deepestChain H r hr A k) := by
  by_cases hk : k < L
  · have heq : (fun A : Params H => deepestChain H r hr A k)
        = fun A => Matrix.reindex (deepestChainSplit H r hr k) (deepestChainSplit H r hr (k + 1))
            (Matrix.reindex (finCongr (deepestChainWidth_castSucc H k hk))
              (finCongr (deepestChainWidth_succ H k hk)) (A ⟨k, hk⟩)) := by
      funext A; rw [deepestChain, deepestChainLayer, dif_pos hk]
    rw [heq]
    exact ((continuous_apply (⟨k, hk⟩ : Fin L)).matrix_reindex _ _).matrix_reindex _ _
  · have heq : (fun A : Params H => deepestChain H r hr A k)
        = fun _ => deepestChain H r hr 0 k := by
      funext A; simp only [deepestChain, deepestChainLayer, dif_neg hk]
    rw [heq]; exact continuous_const

/-- Continuity of the decode-chain partial product `A ↦ partProd (deepestChain H r hr A) k` in `A`
(induction on `k`: base is the constant `1`, step is a matrix multiplication of continuous
families). -/
theorem continuous_partProd_deepestChain (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (k : ℕ) :
    Continuous (fun A : Params H => partProd (deepestChain H r hr A) k) := by
  induction k with
  | zero =>
      have heq : (fun A : Params H => partProd (deepestChain H r hr A) 0)
          = fun _ => (1 : Matrix (Fin r ⊕ Fin (deepestChainWidth H 0 - r))
              (Fin r ⊕ Fin (deepestChainWidth H 0 - r)) ℝ) := rfl
      rw [heq]; exact continuous_const
  | succ k ih =>
      have heq : (fun A : Params H => partProd (deepestChain H r hr A) (k + 1))
          = fun A => partProd (deepestChain H r hr A) k * deepestChain H r hr A k := rfl
      rw [heq]; exact ih.matrix_mul (continuous_deepestChain_layer H r hr k)

/-! ## The `partProd` `(1,1)` basepoint value is a unit (the deepest chain) -/

/-- The decode-chain `partProd` `(1,2)` block vanishes at the deepest point, at every non-last
prefix (`k < L`): induction on `k`, using `deepBlkY = 0` at the layers `< L − 1` (layer 0 +
interiors). The zero `(1,2)` block of the running product lets the `(1,1)` pivot telescope to
`∏ deepBlkA`. -/
theorem partProd_deepestChain_deepestPoint_toBlocks₁₂_eq_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ k, k < L →
      (partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) k).toBlocks₁₂ = 0 := by
  intro k
  induction k with
  | zero => intro _; rw [show partProd _ 0 = 1 from rfl, toBlocks₁₂_one]
  | succ k ih =>
      intro hk
      have hkL : k < L := by omega
      have hik : (partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) k).toBlocks₁₂ = 0 :=
        ih hkL
      -- `(C k).₁₂ = 0`: layer `k` is a non-last layer (`k + 1 < L`), so `deepBlkY k = 0`.
      have hCk : (deepestChain H r hr (deepestPoint H r B hB hr hL) k).toBlocks₁₂ = 0 := by
        refine deepestChain_toBlocks₁₂_eq_zero_of_cols_vanish H r hr _ k hkL (fun i j hj => ?_)
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · exact deepestPoint_layer0_cols_vanish H r B hB hr hL ⟨k, hkL⟩ (by omega) hk0 i j hj
        · exact deepestPoint_interior_cols_vanish H r B hB hr hL ⟨k, hkL⟩ hkpos (by omega) i j hj
      rw [show partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) (k + 1)
          = partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) k
            * deepestChain H r hr (deepestPoint H r B hB hr hL) k from rfl,
        toBlocks₁₂_mul, hik, hCk, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- **The decode-chain `partProd` `(1,1)` block is a unit at the deepest point**, at every prefix
`k ≤ L`: induction on `k`, the succ-step drops the `(partProd)₁₂ · (C k)₂₁` term (the `(1,2)` block
vanishes at non-last prefixes) leaving `(partProd k)₁₁ · deepBlkA k`, a product of units. -/
theorem partProd_deepestChain_deepestPoint_toBlocks₁₁_isUnit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    ∀ k, k ≤ L →
      IsUnit (partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) k).toBlocks₁₁ := by
  intro k
  induction k with
  | zero => intro _; rw [show partProd _ 0 = 1 from rfl, toBlocks₁₁_one]; exact isUnit_one
  | succ k ih =>
      intro hk
      have hkL : k < L := by omega
      have hik : IsUnit
          (partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) k).toBlocks₁₁ :=
        ih (by omega)
      have h12 : (partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) k).toBlocks₁₂ = 0 :=
        partProd_deepestChain_deepestPoint_toBlocks₁₂_eq_zero H r B hB hr hL k hkL
      -- `(C k).₁₁ = deepBlkA k`.
      have hCk : (deepestChain H r hr (deepestPoint H r B hB hr hL) k).toBlocks₁₁
          = deepBlkA H r B hB hr hL ⟨k, hkL⟩ :=
        deepestChain_toBlocks₁₁_eq_layer H r hr (deepestPoint H r B hB hr hL) k hkL
      rw [show partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) (k + 1)
          = partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) k
            * deepestChain H r hr (deepestPoint H r B hB hr hL) k from rfl,
        toBlocks₁₁_mul, h12, Matrix.zero_mul, add_zero, hCk]
      exact hik.mul (hDA ⟨k, hkL⟩)

/-! ## The three eventual-`IsUnit` germs -/

/-- **`hLayer` germ.** For `x` near the basepoint, the decode-chain layer `(1,1)` block is a unit,
at every layer `k < L`. Determinant continuity (decode is a continuous linear equiv) + the basepoint
value `deepBlkA k` (a unit by `hDA`). -/
theorem eventually_isUnit_deepestChain_decode_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) (k : ℕ) (hk : k < L) :
    ∀ᶠ x in nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      IsUnit ((deepestChain H r hr ((paramsEquivFlat H).symm x) k).toBlocks₁₁) := by
  refine eventually_isUnit_of_continuousAt_det _ _
    ((((continuous_deepestChain_layer H r hr k).comp
      (continuous_paramsEquivFlat_symm H)).matrix_submatrix _ _).matrix_det).continuousAt ?_
  rw [show (paramsEquivFlat H).symm ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
      = deepestPoint H r B hB hr hL from (paramsEquivFlat H).symm_apply_apply _,
    deepestChain_toBlocks₁₁_eq_layer H r hr (deepestPoint H r B hB hr hL) k hk]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (hDA ⟨k, hk⟩)).ne_zero

/-- **`hPart` germ.** For `x` near the basepoint, the decode-chain `partProd` `(1,1)` block is a
unit, at every prefix `k ≤ L`. Basepoint value `∏_{j<k} deepBlkA j`
(`partProd_deepestChain_deepestPoint_toBlocks₁₁_isUnit`). -/
theorem eventually_isUnit_partProd_deepestChain_decode_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) (k : ℕ) (hk : k ≤ L) :
    ∀ᶠ x in nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      IsUnit ((partProd (deepestChain H r hr ((paramsEquivFlat H).symm x)) k).toBlocks₁₁) := by
  refine eventually_isUnit_of_continuousAt_det _ _
    ((((continuous_partProd_deepestChain H r hr k).comp
      (continuous_paramsEquivFlat_symm H)).matrix_submatrix _ _).matrix_det).continuousAt ?_
  rw [show (paramsEquivFlat H).symm ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
      = deepestPoint H r B hB hr hL from (paramsEquivFlat H).symm_apply_apply _]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (partProd_deepestChain_deepestPoint_toBlocks₁₁_isUnit H r B hB hr hL hDA k hk)).ne_zero

/-- **`hMid11inv` germ.** For `x` near the basepoint, the product-pivot `(1,1)` block
`(reindex (rThr 0) (pivotThr J) (prod (decode x))).toBlocks₁₁` is a unit. At the basepoint
`prod deepestPoint = B`; with `J = frontEmbed` the pivot split collapses to the threshold split, and
`(reindex (rThr 0) (rThr last) B).toBlocks₁₁ = (partProd (deepestChain deepestPoint) L).toBlocks₁₁`
(`pivotFront_toBlocks₁₁_eq_chainCol` + `reindex_prod_eq_partProd`), the `k = L` case of `hPart`. -/
theorem eventually_isUnit_prod_decode_pivot_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr) :
    ∀ᶠ x in nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      IsUnit ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁) := by
  refine eventually_isUnit_of_continuousAt_det _ _ ?cont ?ne
  · -- continuity via `continuous_Mw` at `P0 = 1`, `QL = 1`, `B = 0` (`1·(prod − 0)·1 = prod`).
    have hMw := continuous_Mw H r (0 : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
      (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (1 : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
      (rThresholdSplit r (H 0) (hr 0)) (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
    simp only [Matrix.one_mul, Matrix.mul_one, sub_zero] at hMw
    exact ((hMw.matrix_submatrix _ _).matrix_det).continuousAt
  · rw [show (paramsEquivFlat H).symm ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
        = deepestPoint H r B hB hr hL from (paramsEquivFlat H).symm_apply_apply _,
      show prod H (deepestPoint H r B hB hr hL) = B from (deepestPoint_isDeep H r B hB hr hL).1]
    have heC : pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J
        = rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) := by
      rw [hJfront]; exact pivotThresholdSplit_frontEmbed H r hr
    rw [heC, show B = prod H (deepestPoint H r B hB hr hL) from
        (deepestPoint_isDeep H r B hB hr hL).1.symm,
      pivotFront_toBlocks₁₁_eq_chainCol H r hr (deepestPoint H r B hB hr hL),
      show (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (deepestChainCol H r hr L (Nat.lt_succ_self L))
            (prod H (deepestPoint H r B hB hr hL))).toBlocks₁₁
          = (partProd (deepestChain H r hr (deepestPoint H r B hB hr hL)) L).toBlocks₁₁ from
        congrArg Matrix.toBlocks₁₁ (reindex_prod_eq_partProd H r hr (deepestPoint H r B hB hr hL))]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (partProd_deepestChain_deepestPoint_toBlocks₁₁_isUnit
        H r B hB hr hL hDA L (le_refl L))).ne_zero

/-! ## Bundled germs (the `∀ k` form the `filter_upwards` assembly consumes directly)

The per-`k` germs above intersect over the finite index range into one eventual set carrying all
layers at once — the `∀ k` form `hLayer`/`hPart` are consumed in, at a fixed `x`, after the
`IsUnit → Invertible` conversion. `Finset.eventually_all` over `range L` / `range (L+1)`. -/

/-- **Bundled `hLayer` germ.** All layers `k < L` are simultaneously eventually-unit. -/
theorem eventually_all_isUnit_deepestChain_decode_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    ∀ᶠ x in nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      ∀ k, k < L → IsUnit ((deepestChain H r hr ((paramsEquivFlat H).symm x) k).toBlocks₁₁) := by
  have hper : ∀ k ∈ Finset.range L, ∀ᶠ x in
      nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        IsUnit ((deepestChain H r hr ((paramsEquivFlat H).symm x) k).toBlocks₁₁) :=
    fun k hk => eventually_isUnit_deepestChain_decode_toBlocks₁₁ H r B hB hr hL hDA k
      (Finset.mem_range.mp hk)
  filter_upwards [(Finset.range L).eventually_all.mpr hper] with x hx k hkL
  exact hx k (Finset.mem_range.mpr hkL)

/-- **Bundled `hPart` germ.** All prefixes `k ≤ L` are simultaneously eventually-unit. -/
theorem eventually_all_isUnit_partProd_deepestChain_decode_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    ∀ᶠ x in nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      ∀ k, k ≤ L →
        IsUnit ((partProd (deepestChain H r hr ((paramsEquivFlat H).symm x)) k).toBlocks₁₁) := by
  have hper : ∀ k ∈ Finset.range (L + 1), ∀ᶠ x in
      nhds ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        IsUnit ((partProd (deepestChain H r hr ((paramsEquivFlat H).symm x)) k).toBlocks₁₁) :=
    fun k hk => eventually_isUnit_partProd_deepestChain_decode_toBlocks₁₁ H r B hB hr hL hDA k
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  filter_upwards [(Finset.range (L + 1)).eventually_all.mpr hper] with x hx k hkL
  exact hx k (Finset.mem_range.mpr (Nat.lt_succ_of_le hkL))

end DLNFibre.DLN.RLCT
