import DLNFibre.DLN.RLCT.Validate.D1HChartFlatten
import DLNFibre.DLN.RLCT.Foundations.S1InverseDerivEquiv
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import DLNFibre.Core.CommonPivotL2
import DLNFibre.Core.SchurProductFactor
import DLNFibre.Core.SchurRankZero

/-!
# `DLNFibre.DLN.RLCT.Validate.D1L2PhiExpl` — foundation for the L = 2 explicit Schur chart crux

The FIRST-tide foundation for the sole remaining L = 2 headline crux `d1ge_L2_hAtV_explicit`
(`D1L2ExplicitCoreProducer.lean`). Per the `genm-phiexpl` decomposition (Codex xhigh design consult,
`codex/design-answer.md`, the "LEANEST DECOMPOSITION" list), the crux factors into ten pieces; this
module lands the reachable pure-algebra FOUNDATION (pieces 1, 2, and the algebraic core of piece 8),
wiring the banked bricks, and pins the downstream analytic interface the later tides must hit.

## What this module CLOSES (sorry-free)

* `prod_two_factor_L2` — the L = 2 product bridge `prod H v = v 0 * v 1` (matrix level). The piece-1
  identity that lets the two-factor common-pivot brick (`Core.exists_common_pivot_two_factor`,
  banked) apply to the actual layers `v 0`, `v 1` at an optimal `v`.
* `rank_le_widths_of_prod_L2` — piece 1: from `(prod H v).rank = r`, every width dominates `r`
  (`r ≤ H 0`, `r ≤ H 1`, `r ≤ H 2`), via `rank_mul_le_left/right` + `rank_le_height/width`.
* `exists_common_pivot_L2_at` — piece 2: at an optimal `v` (`prod H v = B`, `B.rank = r`) the banked
  two-factor pivot brick produces a shared row set `I`, internal set `K`, column set `J` (injective,
  size `r`) making BOTH `(v 0 * v 1).submatrix I J` and `(v 0).submatrix I K` invertible — the pivot
  the Schur reparametrisation `w = (p | A0red, A1red | X, Y, U)` consumes.
* `reduced_core_zero_of_product_rank_le` — the algebraic core of piece 8 (the `hfact` slice
  factorisation): combining the two banked Schur bricks (`schur_product_factor` +
  `schur_complement_zero_of_rank_le`), a rank-`≤ r` two-layer product blocked at an invertible pivot
  has vanishing reduced-core factor `A0red · A1red = 0`. This is the review's "`P` must be a zero of
  the reduced core" fact, at the block level: at the exact optimum the Schur complement of `prod`
  equals that of `B` (both `= 0` at rank `r`), so the reduced factors annihilate.

## The remaining OPEN pieces (deferred to later tides — the analytic bulk)

The interface each must hit is PINNED below via an `example` contract against the banked
`dln_hchart_flat` (`D1HChartFlatten`). In dependency order (Codex list, `[build]` effort):

  3. `blockFlatEquiv_L2` [med, THE cost driver] — `(Fin (flatDim H) → ℝ) ≃L[ℝ]` the block-structured
     product type at the pivot `(I, K, J)`. Localizes all `Fin r ⊕ Fin (H_s − r)` casts.
  4. `Φ_expl` + `schurChartRaw_contDiffOn` [med] — the explicit rational corner-elimination forward
     map `(p | A0red, A1red | X, Y, U)`, `ContDiffOn ℝ 2` on `{det X ≠ 0} ∩ {det M11 ≠ 0}`
     (`ContDiffOn.inv` on the pivot minors), bump-globalised via
     `exists_contDiff_eventuallyEq_of_contDiffOn`.
  5. invertible derivative [DONE — brick A `derivEquiv_of_eventual_inverse`], fed the two Schur
     two-sided inverse germ identities (matrix algebra).
  6. `schurChart_global` [med] — assemble the global `Φ` + its `f'` (brick A) + `hfix`.
  7. `schur_loss_germ_L2` [HIGH, highest line-count risk] — `lossFlatShift H B v =ᶠ[𝓝 0] F ∘ Φ`.
  8. `schur_slice_factor_L2` [med] — `∑ qₑ(0,t)² = dlnLoss (H − r) 0 (core t)` (algebraic core
     CLOSED here as `reduced_core_zero_of_product_rank_le`; the `qₑ`-shaped restatement needs the
     defined `qₑ`).
  9. `schur_slice_hRne_L2` [HIGH] — under `hpos`, `hRne` from `dlnLoss_deepest_core_ae_ne_zero` /
     `MvPolynomial.ae_eval_ne_zero` (banked).
  10. `d1ge_L2_hAtV_explicit` via `d1ge_L2_hAtV_of_explicit_chart` [low, Option A: `e = refl`,
      `u ≡ 1`] — the final wiring.

NOTE (single-writer): this module is NOT yet imported by the aggregator `DLNFibre.lean`; nor are the
banked bricks `Core.CommonPivotL2` / `S1InverseDerivEquiv`. Controller: wire all three when
integrating.
-/

open Matrix MeasureTheory
open scoped ENNReal Topology BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Piece 1 — the L = 2 product bridge and the width bounds -/

/-- The first `L = 2` layer with its width pinned to the literal `H 0 × H 1` (definitionally `v 0`).
The pin makes the two-factor product form without the dependent-`Fin` `HMul` synthesis snag — the
native col type `H (Fin.succ 0)` and row type `H (Fin.castSucc 1)` are defeq but not syntactically
equal, so instance search on raw `v 0 * v 1` fails; here both middles are literally `Fin (H 1)`. -/
def layer0_L2 (H : Fin (2 + 1) → ℕ) (v : Params H) : Matrix (Fin (H 0)) (Fin (H 1)) ℝ := v 0

/-- The second `L = 2` layer, width pinned to the literal `H 1 × H 2` (definitionally `v 1`). -/
def layer1_L2 (H : Fin (2 + 1) → ℕ) (v : Params H) : Matrix (Fin (H 1)) (Fin (H 2)) ℝ := v 1

/-- **The L = 2 layer-product entry form** `(prod H v) i j = ∑ k, v 0 i k · v 1 k j` — the explicit
two-matrix product, entrywise (a scalar sum, so no matrix-`HMul` synthesis fires). Proved from the
`prodAux` unfold, mirroring the banked `prod_two_layer221`. -/
theorem prod_apply_two_factor_L2 (H : Fin (2 + 1) → ℕ) (v : Params H)
    (i : Fin (H 0)) (j : Fin (H (Fin.last 2))) :
    prod H v i j = ∑ k : Fin (H 1), v 0 i k * v 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  congr 2
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (v 0)))) i) k1 using 2

/-- **The L = 2 product bridge** `prod H v = layer0_L2 H v * layer1_L2 H v` (matrix level). The
two-factor matrix product of the width-pinned layers (so the shared middle index is the literal
`Fin (H 1)` on both sides — past the dependent-`Fin` `HMul` snag). Proved entrywise via
`prod_apply_two_factor_L2` + `Matrix.mul_apply`, with `layer{0,1}_L2` defeq `v {0,1}`. This lets the
banked two-factor common-pivot brick apply to the actual layers. -/
theorem prod_two_factor_L2 (H : Fin (2 + 1) → ℕ) (v : Params H) :
    prod H v = layer0_L2 H v * layer1_L2 H v := by
  ext i j
  rw [Matrix.mul_apply, prod_apply_two_factor_L2 H v i j]
  rfl

/-- **Piece 1 (width bounds).** If the two-layer product has rank `r`, every width dominates `r`:
`r ≤ H 0`, `r ≤ H 1`, `r ≤ H 2`. From `rank (v0·v1) ≤ rank v0 ≤ min (H 0) (H 1)` and
`rank (v0·v1) ≤ rank v1 ≤ H 2`. (The crux carries the stronger `hpos : ∀ s, r < H s`; this is the
standalone reusable bound from the rank alone.) -/
theorem rank_le_widths_of_prod_L2 (H : Fin (2 + 1) → ℕ) (v : Params H) (r : ℕ)
    (hr : (prod H v).rank = r) :
    r ≤ H 0 ∧ r ≤ H 1 ∧ r ≤ H 2 := by
  -- rewrite `hr` to the width-pinned product `v0 * v1`, then substitute into the goal so the
  -- `rank_mul_le_*`/`rank_le_*` bounds fire at the literal widths `H 0, H 1, H 2`.
  rw [prod_two_factor_L2] at hr
  rw [← hr]
  exact ⟨le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_height _),
    le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_width _),
    le_trans (Matrix.rank_mul_le_right _ _) (Matrix.rank_le_width _)⟩

/-! ## Piece 2 — the common invertible pivot at an optimal `v` -/

/-- **Piece 2 — the common pivot at `v`.** At an optimal `v` (`prod H v = B`, `B.rank = r`), the
banked two-factor pivot brick (`Core.exists_common_pivot_two_factor`, no Cauchy–Binet) produces a
shared row set `I`, internal set `K`, column set `J` (all injective, size `r`) with BOTH
`(prod H v).submatrix I J` and `(v 0).submatrix I K` invertible (nonzero determinant). The former is
the invertible product pivot `M11`; the latter the invertible first-factor pivot `X` — the two the
Schur reparametrisation `w = (p | A0red, A1red | X, Y, U)` needs. -/
theorem exists_common_pivot_L2_at (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hopt : prod H v = B) (hB : B.rank = r) :
    ∃ (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H (Fin.last 2))),
      Function.Injective I ∧ Function.Injective K ∧ Function.Injective J ∧
      ((prod H v).submatrix I J).det ≠ 0 ∧ ((v 0).submatrix I K).det ≠ 0 := by
  have hpv : (prod H v).rank = r := by rw [hopt, hB]
  rw [prod_two_factor_L2] at hpv
  obtain ⟨I, K, J, hI, hK, hJ, hMdet, hXdet⟩ :=
    Core.exists_common_pivot_two_factor (layer0_L2 H v) (layer1_L2 H v) hpv
  exact ⟨I, K, J, hI, hK, hJ, by rw [prod_two_factor_L2 H v]; exact hMdet, hXdet⟩

/-! ## Algebraic core of piece 8 — the reduced-core factor vanishes at the optimum -/

/-- **The reduced-core factor vanishes at a rank-`≤ r` blocked product** (algebraic core of the
`hfact` slice factorisation, combining the two banked Schur bricks). With `A0 = [[X,Y],[Z,W]]`,
`A1 = [[S,T],[Uu,V]]` blocked at an invertible pivot `X` and invertible product pivot
`M11 = X·S + Y·Uu`, if the reblocked product `A0·A1 = fromBlocks M11 (X·T+Y·V) (Z·S+W·Uu) (Z·T+W·V)`
has rank `≤ r`, then the reduced-core factor annihilates:

    (W − Z·⅟X·Y) · (V − Uu·⅟M11·(X·T + Y·V)) = 0.

Proof: `schur_product_factor` gives the product's Schur complement `= A0red · A1red`;
`schur_complement_zero_of_rank_le` gives the same Schur complement `= 0` at rank `≤ r`. So at an
exact optimum (`prod = B`, `rank B = r`), the reduced core `(A0red, A1red)` is a ZERO of
`dlnLoss (H−r) 0` — the review's "`P` must be a zero of the reduced core" fact. -/
theorem reduced_core_zero_of_product_rank_le {r p q p' : ℕ}
    (X : Matrix (Fin r) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin p) ℝ)
    (Z : Matrix (Fin q) (Fin r) ℝ) (W : Matrix (Fin q) (Fin p) ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ) (T : Matrix (Fin r) (Fin p') ℝ)
    (Uu : Matrix (Fin p) (Fin r) ℝ) (V : Matrix (Fin p) (Fin p') ℝ)
    [Invertible X] [Invertible (X * S + Y * Uu)]
    (hrank : (fromBlocks (X * S + Y * Uu) (X * T + Y * V)
        (Z * S + W * Uu) (Z * T + W * V)).rank ≤ r) :
    (W - Z * ⅟X * Y) * (V - Uu * ⅟(X * S + Y * Uu) * (X * T + Y * V)) = 0 := by
  have hfac := Core.schur_product_factor X Y Z W S T Uu V
  have hzero := Core.schur_complement_zero_of_rank_le
    (X * S + Y * Uu) (X * T + Y * V) (Z * S + W * Uu) (Z * T + W * V) hrank
  rw [← hfac, hzero, sub_self]

/-! ## Piece 3 — the block-reindexing coordinate equiv `blockFlatEquiv_L2` (THE cost driver)

The general-width block reparametrisation: the flat coordinates `Fin (flatDim H) → ℝ` are
identified — by a CONTINUOUS ℝ-LINEAR equiv — with the two layer matrices reindexed so that the `r`
pivot rows/columns (selected by the common pivot `I, K, J` of `exists_common_pivot_L2_at`) sit in
the top-left `Fin r ⊕ Fin (H_s − r)` block. This localises all `Fin r ⊕ Fin (H_s − r)` block-index
casts in ONE equiv, whose `toBlocks₁₁` reads exactly the pivot minor
(`blockFlatEquiv_L2_toBlocks₁₁_fst`), so the Schur bricks (`schur_product_factor`,
`schur_complement_zero_of_rank_le`) apply to the chart image with no further index bookkeeping. It is
a pure REINDEX (no nonlinear chart yet) — the rational corner-elimination `Φ_expl` rides on this.

Characterisations are stated against the LINEAR flatten-inverse `(paramsEquivFlatLinear H).symm`; it
agrees with the measurable `(paramsEquivFlat H).symm` as a function
(`paramsEquivFlatLinear_symm_coe`, `D1HChartRank`), so the germ connecting to `lossFlatShift` bridges
by that one rewrite. -/

/-- **Split a finite index by an injection.** From an injection `σ : Fin r → Fin n`, the equiv
`Fin r ⊕ Fin (n − r) ≃ Fin n` sending the left summand onto the image of `σ` (`sumSplit_inl`) and
the right summand onto the complement. Built from `Equiv.ofInjective` on the image and a cardinality
equiv `Fin (n − r) ≃ ↥(range σ)ᶜ` glued by `Equiv.Set.sumCompl`. The distinguished left `Fin r`
block is the pivot placement the Schur chart consumes. -/
noncomputable def sumSplit {r n : ℕ} (σ : Fin r → Fin n) (hσ : Function.Injective σ) :
    Fin r ⊕ Fin (n - r) ≃ Fin n :=
  (Equiv.sumCongr (Equiv.ofInjective σ hσ)
      (Fintype.equivOfCardEq (by
        have hcard : Fintype.card ↥(Set.range σ) = r := by
          rw [Fintype.card_congr (Equiv.ofInjective σ hσ).symm]; exact Fintype.card_fin r
        rw [Fintype.card_fin, Fintype.card_compl_set, Fintype.card_fin, hcard]))).trans
    (Equiv.Set.sumCompl (Set.range σ))

/-- `sumSplit` sends the left summand `Sum.inl a` to `σ a` — the defining property. -/
@[simp] theorem sumSplit_inl {r n : ℕ} (σ : Fin r → Fin n) (hσ : Function.Injective σ) (a : Fin r) :
    sumSplit σ hσ (Sum.inl a) = σ a := by
  simp only [sumSplit, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl]
  rfl

/-- The block-decomposed L = 2 parameter type at a rank-`r` pivot: the two layer matrices reindexed
so the `r` pivot rows/columns sit in the top-left `Fin r ⊕ Fin (H_s − r)` block. -/
abbrev BlockParamsL2 (H : Fin (2 + 1) → ℕ) (r : ℕ) : Type :=
  Matrix (Fin r ⊕ Fin (H 0 - r)) (Fin r ⊕ Fin (H 1 - r)) ℝ ×
  Matrix (Fin r ⊕ Fin (H 1 - r)) (Fin r ⊕ Fin (H 2 - r)) ℝ

/-- **The L = 2 layer split** `Params H ≃ₗ[ℝ] (v 0) × (v 1)`, at literal widths (the `def` return
type pins `(0 : Fin 2).castSucc = 0`, `.succ = 1`, `(1 : Fin 2).castSucc = 1`, `.succ = 2`). The
dependent `Fin 2` product `LinearEquiv.piFinTwo`, ascribed to the clean layer types. -/
noncomputable def paramsSplitL2 (H : Fin (2 + 1) → ℕ) :
    Params H ≃ₗ[ℝ] (Matrix (Fin (H 0)) (Fin (H 1)) ℝ) × (Matrix (Fin (H 1)) (Fin (H 2)) ℝ) :=
  LinearEquiv.piFinTwo ℝ (fun s : Fin 2 => Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ)

/-- **`blockFlatEquiv_L2` — the general-width block-reindexing coordinate model (piece 3).** A
CONTINUOUS ℝ-linear equiv `(Fin (flatDim H) → ℝ) ≃L[ℝ] BlockParamsL2 H r`: flatten-inverse (linear)
`≫` layer split `≫` per-layer reindex by the pivot injections `I, K, J` (each `Fin (H_s) ≃ Fin r ⊕
Fin (H_s − r)` via `sumSplit`). Continuous by `LinearEquiv.toContinuousLinearEquiv` (all spaces are
finite-dimensional). The two layer blocks read off via `blockFlatEquiv_L2_fst` / `_snd`; the pivot
`r × r` minor is `blockFlatEquiv_L2_toBlocks₁₁_fst`. -/
noncomputable def blockFlatEquiv_L2 (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H 2))
    (hI : Function.Injective I) (hK : Function.Injective K) (hJ : Function.Injective J) :
    (Fin (flatDim H) → ℝ) ≃L[ℝ] BlockParamsL2 H r :=
  ((paramsEquivFlatLinear H).symm.trans
    ((paramsSplitL2 H).trans
      ((Matrix.reindexLinearEquiv ℝ ℝ (sumSplit I hI).symm (sumSplit K hK).symm).prodCongr
        (Matrix.reindexLinearEquiv ℝ ℝ (sumSplit K hK).symm
          (sumSplit J hJ).symm)))).toContinuousLinearEquiv

/-- The first block of `blockFlatEquiv_L2 x` is the pivot-reindexed first layer of the (linear)
flatten-inverse of `x`. -/
theorem blockFlatEquiv_L2_fst (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H 2))
    (hI : Function.Injective I) (hK : Function.Injective K) (hJ : Function.Injective J)
    (x : Fin (flatDim H) → ℝ) :
    (blockFlatEquiv_L2 H r I K J hI hK hJ x).1
      = Matrix.reindex (sumSplit I hI).symm (sumSplit K hK).symm
          ((paramsEquivFlatLinear H).symm x 0) := by
  rw [blockFlatEquiv_L2]; rfl

/-- The second block of `blockFlatEquiv_L2 x` is the pivot-reindexed second layer of the (linear)
flatten-inverse of `x`. -/
theorem blockFlatEquiv_L2_snd (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H 2))
    (hI : Function.Injective I) (hK : Function.Injective K) (hJ : Function.Injective J)
    (x : Fin (flatDim H) → ℝ) :
    (blockFlatEquiv_L2 H r I K J hI hK hJ x).2
      = Matrix.reindex (sumSplit K hK).symm (sumSplit J hJ).symm
          ((paramsEquivFlatLinear H).symm x 1) := by
  rw [blockFlatEquiv_L2]; rfl

/-- **The pivot `r × r` block is the pivot minor.** The `toBlocks₁₁` corner of the first block of
`blockFlatEquiv_L2 x` is exactly the first-layer minor at the pivot rows `I`, columns `K` — the
invertible pivot `X` the Schur reparametrisation consumes (invertibility from
`exists_common_pivot_L2_at`). -/
theorem blockFlatEquiv_L2_toBlocks₁₁_fst (H : Fin (2 + 1) → ℕ) (r : ℕ)
    (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H 2))
    (hI : Function.Injective I) (hK : Function.Injective K) (hJ : Function.Injective J)
    (x : Fin (flatDim H) → ℝ) :
    (blockFlatEquiv_L2 H r I K J hI hK hJ x).1.toBlocks₁₁
      = ((paramsEquivFlatLinear H).symm x 0).submatrix I K := by
  rw [blockFlatEquiv_L2_fst]
  ext a b
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, sumSplit_inl]

/-! ## Interface contract — the shape the OPEN pieces (3–7) must hit (durable next-tide target)

The flat chart-transfer assembly point the crux routes through, pinned as an `example` contract (it
references the existing banked `dln_hchart_flat`, so it type-checks with no `sorry`). The next-tide
`Φ_expl`/germ build must produce the hypotheses below (`ContDiff ℝ 2 Φ`, invertible `f'`, the fixed
point, and the germ `lossFlatShift =ᶠ F ∘ Φ`) and then reindex its `F` into the product form the
consumer `d1ge_L2_hAtV_of_explicit_chart` reads (Option A: `e = refl`, `u ≡ 1`). -/
example (H : Fin (L + 1) → ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (F : (Fin (flatDim H) → ℝ) → ℝ) (Φ : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (f' : (Fin (flatDim H) → ℝ) ≃L[ℝ] (Fin (flatDim H) → ℝ))
    (hΦ : ContDiff ℝ 2 Φ)
    (hΦ' : HasFDerivAt Φ (f' : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
      (0 : Fin (flatDim H) → ℝ))
    (hfix : Φ (0 : Fin (flatDim H) → ℝ) = 0)
    (hgerm : lossFlatShift H B v =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)] fun w ↦ F (Φ w)) :
    rlctAt H (dlnLoss H B) v = rlctAtOn F (0 : Fin (flatDim H) → ℝ) :=
  dln_hchart_flat H B v F Φ f' hΦ hΦ' hfix hgerm

end DLNFibre.DLN.RLCT
