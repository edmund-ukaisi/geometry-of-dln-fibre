import DLNFibre.DLN.RLCT.Validate.D1HChartFlatten
import DLNFibre.DLN.RLCT.Foundations.S1InverseDerivEquiv
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import DLNFibre.Core.CommonPivotL2
import DLNFibre.Core.SchurProductFactor
import DLNFibre.Core.SchurRankZero
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed

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

/-! ## Piece 2 of the next-tide order — the explicit rational corner-elimination chart `Φ_expl`

The block corner-elimination forward map on `BlockParamsL2 H r`, its explicit rational two-sided
inverse, the block readbacks, and the det→`Invertible` bridge. `schurChartRaw` is the raw
(un-globalised) chart `Φ_expl` in the `blockFlatEquiv_L2` coordinates.

Given the two layer matrices blocked at the common pivot as `A0 = [[X,Y],[Z,W]]`,
`A1 = [[S,T],[Uu,V]]` (blocks read by `toBlocks₁₁/₁₂/₂₁/₂₂`), the chart reparametrises to
`(X, Y, Uu | M11, M12, M21 | A0red, A1red)`, where the product corners
`M11 = X S + Y Uu`, `M12 = X T + Y V`, `M21 = Z S + W Uu` are the regular directions and
`A0red = W − Z X⁻¹ Y`, `A1red = V − Uu M11⁻¹ M12` the reduced-core factors (the Schur bricks read
these). Both `X⁻¹` and `M11⁻¹` are the Mathlib nonsingular inverse (`Matrix.inv`), rational in the
pivot determinants — so the map and its inverse are `C²` on `{det X ≠ 0} ∩ {det M11 ≠ 0}`.

Output placement: first matrix `= fromBlocks X Y M21 A0red`, second `= fromBlocks M11 M12 Uu A1red`
(so the whole output is again a `BlockParamsL2 H r`, and `A0red, A1red` are the `toBlocks₂₂` corners). -/

/-- **The block corner-elimination forward map** (the raw chart `Φ_expl` in block coordinates). -/
noncomputable def schurChartRaw (H : Fin (2 + 1) → ℕ) (r : ℕ) :
    BlockParamsL2 H r → BlockParamsL2 H r := fun P =>
  let X := P.1.toBlocks₁₁; let Y := P.1.toBlocks₁₂; let Z := P.1.toBlocks₂₁; let W := P.1.toBlocks₂₂
  let S := P.2.toBlocks₁₁; let T := P.2.toBlocks₁₂; let Uu := P.2.toBlocks₂₁; let V := P.2.toBlocks₂₂
  let M11 := X * S + Y * Uu
  let M12 := X * T + Y * V
  (Matrix.fromBlocks X Y (Z * S + W * Uu) (W - Z * X⁻¹ * Y),
   Matrix.fromBlocks M11 M12 Uu (V - Uu * M11⁻¹ * M12))

/-- **The explicit rational inverse** `Ψ_expl` of the corner-elimination chart. Reading the output
coordinates `(X, Y, M21, A0red | M11, M12, Uu, A1red)`, it reconstructs the layer blocks by
`S = X⁻¹(M11 − Y Uu)`, `V = A1red + Uu M11⁻¹ M12`, `T = X⁻¹(M12 − Y V)`,
`Z = (M21 − A0red Uu) M11⁻¹ X`, `W = A0red + (M21 − A0red Uu) M11⁻¹ Y` — rational in `det X`,
`det M11`. -/
noncomputable def schurChartRawInv (H : Fin (2 + 1) → ℕ) (r : ℕ) :
    BlockParamsL2 H r → BlockParamsL2 H r := fun Q =>
  let X := Q.1.toBlocks₁₁; let Y := Q.1.toBlocks₁₂; let M21 := Q.1.toBlocks₂₁; let A0red := Q.1.toBlocks₂₂
  let M11 := Q.2.toBlocks₁₁; let M12 := Q.2.toBlocks₁₂; let Uu := Q.2.toBlocks₂₁; let A1red := Q.2.toBlocks₂₂
  let V := A1red + Uu * M11⁻¹ * M12
  (Matrix.fromBlocks X Y ((M21 - A0red * Uu) * M11⁻¹ * X) (A0red + (M21 - A0red * Uu) * M11⁻¹ * Y),
   Matrix.fromBlocks (X⁻¹ * (M11 - Y * Uu)) (X⁻¹ * (M12 - Y * V)) Uu V)

/-! ### Block readbacks (all `rfl` — `toBlocks (fromBlocks …)` is definitional) -/

variable {H : Fin (2 + 1) → ℕ} {r : ℕ}

@[simp] theorem schurChartRaw_fst_toBlocks₁₁ (P : BlockParamsL2 H r) :
    (schurChartRaw H r P).1.toBlocks₁₁ = P.1.toBlocks₁₁ := rfl

@[simp] theorem schurChartRaw_fst_toBlocks₁₂ (P : BlockParamsL2 H r) :
    (schurChartRaw H r P).1.toBlocks₁₂ = P.1.toBlocks₁₂ := rfl

@[simp] theorem schurChartRaw_fst_toBlocks₂₁ (P : BlockParamsL2 H r) :
    (schurChartRaw H r P).1.toBlocks₂₁
      = P.1.toBlocks₂₁ * P.2.toBlocks₁₁ + P.1.toBlocks₂₂ * P.2.toBlocks₂₁ := rfl

@[simp] theorem schurChartRaw_fst_toBlocks₂₂ (P : BlockParamsL2 H r) :
    (schurChartRaw H r P).1.toBlocks₂₂
      = P.1.toBlocks₂₂ - P.1.toBlocks₂₁ * P.1.toBlocks₁₁⁻¹ * P.1.toBlocks₁₂ := rfl

@[simp] theorem schurChartRaw_snd_toBlocks₁₁ (P : BlockParamsL2 H r) :
    (schurChartRaw H r P).2.toBlocks₁₁
      = P.1.toBlocks₁₁ * P.2.toBlocks₁₁ + P.1.toBlocks₁₂ * P.2.toBlocks₂₁ := rfl

@[simp] theorem schurChartRaw_snd_toBlocks₁₂ (P : BlockParamsL2 H r) :
    (schurChartRaw H r P).2.toBlocks₁₂
      = P.1.toBlocks₁₁ * P.2.toBlocks₁₂ + P.1.toBlocks₁₂ * P.2.toBlocks₂₂ := rfl

@[simp] theorem schurChartRaw_snd_toBlocks₂₁ (P : BlockParamsL2 H r) :
    (schurChartRaw H r P).2.toBlocks₂₁ = P.2.toBlocks₂₁ := rfl

@[simp] theorem schurChartRaw_snd_toBlocks₂₂ (P : BlockParamsL2 H r) :
    (schurChartRaw H r P).2.toBlocks₂₂
      = P.2.toBlocks₂₂ - P.2.toBlocks₂₁
          * (P.1.toBlocks₁₁ * P.2.toBlocks₁₁ + P.1.toBlocks₁₂ * P.2.toBlocks₂₁)⁻¹
          * (P.1.toBlocks₁₁ * P.2.toBlocks₁₂ + P.1.toBlocks₁₂ * P.2.toBlocks₂₂) := rfl

@[simp] theorem schurChartRawInv_fst_toBlocks₁₁ (Q : BlockParamsL2 H r) :
    (schurChartRawInv H r Q).1.toBlocks₁₁ = Q.1.toBlocks₁₁ := rfl

@[simp] theorem schurChartRawInv_fst_toBlocks₁₂ (Q : BlockParamsL2 H r) :
    (schurChartRawInv H r Q).1.toBlocks₁₂ = Q.1.toBlocks₁₂ := rfl

@[simp] theorem schurChartRawInv_fst_toBlocks₂₁ (Q : BlockParamsL2 H r) :
    (schurChartRawInv H r Q).1.toBlocks₂₁
      = (Q.1.toBlocks₂₁ - Q.1.toBlocks₂₂ * Q.2.toBlocks₂₁) * Q.2.toBlocks₁₁⁻¹ * Q.1.toBlocks₁₁ := rfl

@[simp] theorem schurChartRawInv_fst_toBlocks₂₂ (Q : BlockParamsL2 H r) :
    (schurChartRawInv H r Q).1.toBlocks₂₂
      = Q.1.toBlocks₂₂ + (Q.1.toBlocks₂₁ - Q.1.toBlocks₂₂ * Q.2.toBlocks₂₁) * Q.2.toBlocks₁₁⁻¹ * Q.1.toBlocks₁₂ := rfl

@[simp] theorem schurChartRawInv_snd_toBlocks₁₁ (Q : BlockParamsL2 H r) :
    (schurChartRawInv H r Q).2.toBlocks₁₁
      = Q.1.toBlocks₁₁⁻¹ * (Q.2.toBlocks₁₁ - Q.1.toBlocks₁₂ * Q.2.toBlocks₂₁) := rfl

@[simp] theorem schurChartRawInv_snd_toBlocks₁₂ (Q : BlockParamsL2 H r) :
    (schurChartRawInv H r Q).2.toBlocks₁₂
      = Q.1.toBlocks₁₁⁻¹ * (Q.2.toBlocks₁₂
          - Q.1.toBlocks₁₂ * (Q.2.toBlocks₂₂ + Q.2.toBlocks₂₁ * Q.2.toBlocks₁₁⁻¹ * Q.2.toBlocks₁₂)) := rfl

@[simp] theorem schurChartRawInv_snd_toBlocks₂₁ (Q : BlockParamsL2 H r) :
    (schurChartRawInv H r Q).2.toBlocks₂₁ = Q.2.toBlocks₂₁ := rfl

@[simp] theorem schurChartRawInv_snd_toBlocks₂₂ (Q : BlockParamsL2 H r) :
    (schurChartRawInv H r Q).2.toBlocks₂₂
      = Q.2.toBlocks₂₂ + Q.2.toBlocks₂₁ * Q.2.toBlocks₁₁⁻¹ * Q.2.toBlocks₁₂ := rfl

/-! ### det → `Invertible` transport

On the chart domain `det X ≠ 0`, `det M11 ≠ 0`; over ℝ (a field) these give `IsUnit` of the
determinant, hence the nonsingular-inverse cancellations `X * X⁻¹ = 1` etc. and, when the Schur
bricks need it, an `Invertible` instance with `⅟X = X⁻¹` (`Matrix.invOf_eq_nonsing_inv`). -/

/-- A square real matrix with nonzero determinant is `Invertible` (its `⅟` is `Matrix.inv`). -/
@[reducible] noncomputable def invertibleOfDetNeZero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : A.det ≠ 0) : Invertible A :=
  A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr h)

/-! ### The exact rational two-sided inverse

`schurChartRawInv` is a genuine two-sided inverse of `schurChartRaw` on
`{det X ≠ 0} ∩ {det M11 ≠ 0}` — the coordinates form a rational diffeomorphism there. The two
identities are pure block matrix algebra (the four cancellations `X⁻¹X = 1`, `X X⁻¹ = 1`,
`M11⁻¹ M11 = 1`, `M11 M11⁻¹ = 1` from the two determinant hypotheses). The `blockFlatEquiv_L2`
conjugation + germ restriction (piece 3, next tide) turns these into the `=ᶠ[𝓝 0]` identities
`derivEquiv_of_eventual_inverse` (brick A) consumes for the invertible chart derivative. -/

/-! #### Abstract block-algebra reconstructions (`Ψ ∘ Φ = id`)

The five nontrivial block equalities for `schurChartRawInv (schurChartRaw P) = P`, stated over abstract
blocks `X, Y, Z, W, S, T, Uu, V` with the two determinant `IsUnit` hypotheses. Pure matrix algebra
(the `X⁻¹X = 1`, `M11⁻¹M11 = 1`, `X X⁻¹ = 1`, `M11 M11⁻¹ = 1` cancellations + additive rearrangement). -/

section ReconInv
variable {p q p' : ℕ}
variable {X : Matrix (Fin r) (Fin r) ℝ} {Y : Matrix (Fin r) (Fin p) ℝ}
  {Z : Matrix (Fin q) (Fin r) ℝ} {W : Matrix (Fin q) (Fin p) ℝ}
  {S : Matrix (Fin r) (Fin r) ℝ} {T : Matrix (Fin r) (Fin p') ℝ}
  {Uu : Matrix (Fin p) (Fin r) ℝ} {V : Matrix (Fin p) (Fin p') ℝ}

/-- Reconstruct `S` from `M11 = X S + Y Uu`: `X⁻¹(M11 − Y Uu) = S`. -/
theorem recon_S (hXu : IsUnit X.det) :
    X⁻¹ * ((X * S + Y * Uu) - Y * Uu) = S := by
  have h1 : (X * S + Y * Uu) - Y * Uu = X * S := by abel
  rw [h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul X hXu, Matrix.one_mul]

/-- Reconstruct `V` from `A1red = V − Uu M11⁻¹ M12`: `(V − Uu M11⁻¹ M12) + Uu M11⁻¹ M12 = V`. -/
theorem recon_V :
    (V - Uu * (X * S + Y * Uu)⁻¹ * (X * T + Y * V))
      + Uu * (X * S + Y * Uu)⁻¹ * (X * T + Y * V) = V := by
  abel

/-- Reconstruct `T` from `M12 = X T + Y V` (after `V` is recovered): `X⁻¹(M12 − Y V) = T`. -/
theorem recon_T (hXu : IsUnit X.det) :
    X⁻¹ * ((X * T + Y * V)
        - Y * ((V - Uu * (X * S + Y * Uu)⁻¹ * (X * T + Y * V))
          + Uu * (X * S + Y * Uu)⁻¹ * (X * T + Y * V))) = T := by
  have hV : (V - Uu * (X * S + Y * Uu)⁻¹ * (X * T + Y * V))
      + Uu * (X * S + Y * Uu)⁻¹ * (X * T + Y * V) = V := by abel
  rw [hV]
  have h2 : (X * T + Y * V) - Y * V = X * T := by abel
  rw [h2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul X hXu, Matrix.one_mul]

/-- Reconstruct `Z` from `M21 = Z S + W Uu`, `A0red = W − Z X⁻¹ Y`:
`(M21 − A0red Uu) M11⁻¹ X = Z`. -/
theorem recon_Z (hXu : IsUnit X.det) (hMu : IsUnit (X * S + Y * Uu).det) :
    ((Z * S + W * Uu) - (W - Z * X⁻¹ * Y) * Uu) * (X * S + Y * Uu)⁻¹ * X = Z := by
  have hZXX : Z * X⁻¹ * X = Z := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul X hXu, Matrix.mul_one]
  have expand : Z * X⁻¹ * (X * S + Y * Uu) = Z * S + Z * X⁻¹ * Y * Uu := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc (Z * X⁻¹) X S, hZXX, ← Matrix.mul_assoc (Z * X⁻¹) Y Uu]
  have hL : (Z * S + W * Uu) - (W - Z * X⁻¹ * Y) * Uu = Z * X⁻¹ * (X * S + Y * Uu) := by
    rw [expand, Matrix.sub_mul]; abel
  rw [hL, Matrix.mul_assoc (Z * X⁻¹) (X * S + Y * Uu) (X * S + Y * Uu)⁻¹,
    Matrix.mul_nonsing_inv _ hMu, Matrix.mul_one, hZXX]

/-- Reconstruct `W` from `A0red = W − Z X⁻¹ Y`:
`A0red + (M21 − A0red Uu) M11⁻¹ Y = W`. -/
theorem recon_W (hXu : IsUnit X.det) (hMu : IsUnit (X * S + Y * Uu).det) :
    (W - Z * X⁻¹ * Y)
      + ((Z * S + W * Uu) - (W - Z * X⁻¹ * Y) * Uu) * (X * S + Y * Uu)⁻¹ * Y = W := by
  have hZXX : Z * X⁻¹ * X = Z := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul X hXu, Matrix.mul_one]
  have expand : Z * X⁻¹ * (X * S + Y * Uu) = Z * S + Z * X⁻¹ * Y * Uu := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc (Z * X⁻¹) X S, hZXX, ← Matrix.mul_assoc (Z * X⁻¹) Y Uu]
  have hL : (Z * S + W * Uu) - (W - Z * X⁻¹ * Y) * Uu = Z * X⁻¹ * (X * S + Y * Uu) := by
    rw [expand, Matrix.sub_mul]; abel
  have hsnd : ((Z * S + W * Uu) - (W - Z * X⁻¹ * Y) * Uu) * (X * S + Y * Uu)⁻¹ * Y = Z * X⁻¹ * Y := by
    rw [hL, Matrix.mul_assoc (Z * X⁻¹) (X * S + Y * Uu) (X * S + Y * Uu)⁻¹,
      Matrix.mul_nonsing_inv _ hMu, Matrix.mul_one]
  rw [hsnd]; abel

end ReconInv

/-! #### Abstract block-algebra recomputations (`Φ ∘ Ψ = id`)

The five nontrivial block equalities for `schurChartRaw (schurChartRawInv Q) = Q`, over abstract output
coordinates `X, Y, M21, A0red, M11, M12, Uu, A1red` with `IsUnit X.det`, `IsUnit M11.det`. -/

section ReconFwd
variable {p q p' : ℕ}
variable {X : Matrix (Fin r) (Fin r) ℝ} {Y : Matrix (Fin r) (Fin p) ℝ}
  {M21 : Matrix (Fin q) (Fin r) ℝ} {A0red : Matrix (Fin q) (Fin p) ℝ}
  {M11 : Matrix (Fin r) (Fin r) ℝ} {M12 : Matrix (Fin r) (Fin p') ℝ}
  {Uu : Matrix (Fin p) (Fin r) ℝ} {A1red : Matrix (Fin p) (Fin p') ℝ}

/-- Recompute `M11` from the reconstruction `S = X⁻¹(M11 − Y Uu)`: `X S + Y Uu = M11`. -/
theorem reconOut_M11 (hXu : IsUnit X.det) :
    X * (X⁻¹ * (M11 - Y * Uu)) + Y * Uu = M11 := by
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv X hXu, Matrix.one_mul]; abel

/-- Recompute `M12` from `T = X⁻¹(M12 − Y V)`, `V = A1red + Uu M11⁻¹ M12`: `X T + Y V = M12`. -/
theorem reconOut_M12 (hXu : IsUnit X.det) :
    X * (X⁻¹ * (M12 - Y * (A1red + Uu * M11⁻¹ * M12))) + Y * (A1red + Uu * M11⁻¹ * M12) = M12 := by
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv X hXu, Matrix.one_mul]; abel

/-- Recompute `A0red` from `W = A0red + (M21 − A0red Uu) M11⁻¹ Y`, `Z = (M21 − A0red Uu) M11⁻¹ X`:
`W − Z X⁻¹ Y = A0red`. -/
theorem reconOut_A0red (hXu : IsUnit X.det) :
    (A0red + (M21 - A0red * Uu) * M11⁻¹ * Y) - ((M21 - A0red * Uu) * M11⁻¹ * X) * X⁻¹ * Y = A0red := by
  have hR : ((M21 - A0red * Uu) * M11⁻¹ * X) * X⁻¹ * Y = (M21 - A0red * Uu) * M11⁻¹ * Y := by
    rw [Matrix.mul_assoc ((M21 - A0red * Uu) * M11⁻¹) X X⁻¹, Matrix.mul_nonsing_inv X hXu,
      Matrix.mul_one]
  rw [hR]; abel

/-- Recompute `M21` from `Z, W, S`: `Z S + W Uu = M21`. -/
theorem reconOut_M21 (hXu : IsUnit X.det) (hMu : IsUnit M11.det) :
    ((M21 - A0red * Uu) * M11⁻¹ * X) * (X⁻¹ * (M11 - Y * Uu))
      + (A0red + (M21 - A0red * Uu) * M11⁻¹ * Y) * Uu = M21 := by
  have hfst : ((M21 - A0red * Uu) * M11⁻¹ * X) * (X⁻¹ * (M11 - Y * Uu))
      = (M21 - A0red * Uu) * M11⁻¹ * (M11 - Y * Uu) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc ((M21 - A0red * Uu) * M11⁻¹) X X⁻¹,
      Matrix.mul_nonsing_inv X hXu, Matrix.mul_one]
  have hRM11 : (M21 - A0red * Uu) * M11⁻¹ * M11 = M21 - A0red * Uu := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul M11 hMu, Matrix.mul_one]
  rw [hfst, Matrix.mul_sub, Matrix.add_mul, hRM11, ← Matrix.mul_assoc ((M21 - A0red * Uu) * M11⁻¹) Y Uu]
  abel

/-- Recompute `A1red` from the reconstruction (using `M11`, `M12` recomputed): `V − Uu M11⁻¹ M12 =
A1red`. -/
theorem reconOut_A1red (hXu : IsUnit X.det) :
    (A1red + Uu * M11⁻¹ * M12)
      - Uu * (X * (X⁻¹ * (M11 - Y * Uu)) + Y * Uu)⁻¹
        * (X * (X⁻¹ * (M12 - Y * (A1red + Uu * M11⁻¹ * M12))) + Y * (A1red + Uu * M11⁻¹ * M12))
      = A1red := by
  rw [reconOut_M11 hXu, reconOut_M12 hXu]; abel

end ReconFwd

/-! #### Assembly of the two-sided inverse -/

/-- **`Ψ_expl ∘ Φ_expl = id`** on `{det X ≠ 0} ∩ {det M11 ≠ 0}`: the inverse chart reconstructs the
original layer blocks exactly. -/
theorem schurChartRawInv_schurChartRaw (P : BlockParamsL2 H r)
    (hX : (P.1.toBlocks₁₁).det ≠ 0)
    (hM11 : (P.1.toBlocks₁₁ * P.2.toBlocks₁₁ + P.1.toBlocks₁₂ * P.2.toBlocks₂₁).det ≠ 0) :
    schurChartRawInv H r (schurChartRaw H r P) = P := by
  have hXu : IsUnit (P.1.toBlocks₁₁).det := isUnit_iff_ne_zero.mpr hX
  have hMu : IsUnit (P.1.toBlocks₁₁ * P.2.toBlocks₁₁ + P.1.toBlocks₁₂ * P.2.toBlocks₂₁).det :=
    isUnit_iff_ne_zero.mpr hM11
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.ext_iff_blocks]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [schurChartRawInv_fst_toBlocks₂₁, schurChartRaw_fst_toBlocks₁₁,
        schurChartRaw_fst_toBlocks₂₁, schurChartRaw_fst_toBlocks₂₂,
        schurChartRaw_snd_toBlocks₁₁, schurChartRaw_snd_toBlocks₂₁]
      exact recon_Z hXu hMu
    · simp only [schurChartRawInv_fst_toBlocks₂₂,
        schurChartRaw_fst_toBlocks₁₂, schurChartRaw_fst_toBlocks₂₁, schurChartRaw_fst_toBlocks₂₂,
        schurChartRaw_snd_toBlocks₁₁, schurChartRaw_snd_toBlocks₂₁]
      exact recon_W hXu hMu
  · rw [Matrix.ext_iff_blocks]
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp only [schurChartRawInv_snd_toBlocks₁₁, schurChartRaw_fst_toBlocks₁₁,
        schurChartRaw_fst_toBlocks₁₂, schurChartRaw_snd_toBlocks₁₁, schurChartRaw_snd_toBlocks₂₁]
      exact recon_S hXu
    · simp only [schurChartRawInv_snd_toBlocks₁₂, schurChartRaw_fst_toBlocks₁₁,
        schurChartRaw_fst_toBlocks₁₂, schurChartRaw_snd_toBlocks₁₁, schurChartRaw_snd_toBlocks₁₂,
        schurChartRaw_snd_toBlocks₂₁, schurChartRaw_snd_toBlocks₂₂]
      exact recon_T hXu
    · simp only [schurChartRawInv_snd_toBlocks₂₂, schurChartRaw_snd_toBlocks₁₁,
        schurChartRaw_snd_toBlocks₁₂, schurChartRaw_snd_toBlocks₂₁, schurChartRaw_snd_toBlocks₂₂]
      exact recon_V

/-- **`Φ_expl ∘ Ψ_expl = id`** on `{det X ≠ 0} ∩ {det M11 ≠ 0}` (reading the output coordinates): the
forward chart recomputes the regular corners and reduced factors from a reconstruction. -/
theorem schurChartRaw_schurChartRawInv (Q : BlockParamsL2 H r)
    (hX : (Q.1.toBlocks₁₁).det ≠ 0) (hM11 : (Q.2.toBlocks₁₁).det ≠ 0) :
    schurChartRaw H r (schurChartRawInv H r Q) = Q := by
  have hXu : IsUnit (Q.1.toBlocks₁₁).det := isUnit_iff_ne_zero.mpr hX
  have hMu : IsUnit (Q.2.toBlocks₁₁).det := isUnit_iff_ne_zero.mpr hM11
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.ext_iff_blocks]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [schurChartRaw_fst_toBlocks₂₁,
        schurChartRawInv_fst_toBlocks₂₁, schurChartRawInv_fst_toBlocks₂₂,
        schurChartRawInv_snd_toBlocks₁₁, schurChartRawInv_snd_toBlocks₂₁]
      exact reconOut_M21 hXu hMu
    · simp only [schurChartRaw_fst_toBlocks₂₂, schurChartRawInv_fst_toBlocks₁₁,
        schurChartRawInv_fst_toBlocks₁₂, schurChartRawInv_fst_toBlocks₂₁,
        schurChartRawInv_fst_toBlocks₂₂]
      exact reconOut_A0red hXu
  · rw [Matrix.ext_iff_blocks]
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp only [schurChartRaw_snd_toBlocks₁₁, schurChartRawInv_fst_toBlocks₁₁,
        schurChartRawInv_fst_toBlocks₁₂, schurChartRawInv_snd_toBlocks₁₁,
        schurChartRawInv_snd_toBlocks₂₁]
      exact reconOut_M11 hXu
    · simp only [schurChartRaw_snd_toBlocks₁₂, schurChartRawInv_fst_toBlocks₁₁,
        schurChartRawInv_fst_toBlocks₁₂, schurChartRawInv_snd_toBlocks₁₂,
        schurChartRawInv_snd_toBlocks₂₂]
      exact reconOut_M12 hXu
    · simp only [schurChartRaw_snd_toBlocks₂₂, schurChartRawInv_fst_toBlocks₁₁,
        schurChartRawInv_fst_toBlocks₁₂, schurChartRawInv_snd_toBlocks₁₁,
        schurChartRawInv_snd_toBlocks₁₂, schurChartRawInv_snd_toBlocks₂₁,
        schurChartRawInv_snd_toBlocks₂₂]
      exact reconOut_A1red hXu

/-! ## `schurChartRaw` is `C²` on the pivot domain (`schurChartRaw_contDiffOn`)

`schurChartRaw` is a rational map (matrix `+, *, ⁻¹`), so `ContDiffOn ℝ 2` on
`{det X ≠ 0} ∩ {det M11 ≠ 0}` follows entrywise from the smoothness of matrix determinant / adjugate /
inverse / product. This needs a `NormedAddCommGroup` on `BlockParamsL2 H r`; Mathlib does not make the
elementwise matrix norm a global instance, so we `open scoped Matrix.Norms.Elementwise` — SAFE because
its topology is DEFINITIONALLY the product/Pi topology `blockFlatEquiv_L2` already uses (no diamond).
**Consumers of `schurChartRaw_contDiffOn` must also `open scoped Matrix.Norms.Elementwise`.**

The generic entrywise matrix-`ContDiff` helpers (`SchurChartC2`) are copied from
`DeepestSchurSmooth`'s (`contDiff_matrix_det_of_entries` &c.); controller: dedup into a shared
Foundations module on a later pass. -/

namespace SchurChartC2

variable {𝕏 : Type*} [NormedAddCommGroup 𝕏] [NormedSpace ℝ 𝕏]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of an entrywise-`ContDiff` matrix family is `ContDiff`. -/
theorem contDiff_matrix_det_of_entries {A : 𝕏 → Matrix n n ℝ}
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).det) := by
  have heq : (fun x => (A x).det)
      = fun x => ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A x (σ i) i := by
    funext x; rw [Matrix.det_apply]
  rw [heq]
  exact ContDiff.sum (fun σ _ => ContDiff.const_smul _ (contDiff_prod (fun i _ => hA (σ i) i)))

/-- Each adjugate entry of an entrywise-`ContDiff` matrix family is `ContDiff`. -/
theorem contDiff_matrix_adjugate_entry_of_entries {A : 𝕏 → Matrix n n ℝ}
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) (i j : n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).adjugate i j) := by
  have heq : (fun x => (A x).adjugate i j)
      = fun x => ((A x).updateRow j (Pi.single i 1)).det := by
    funext x; rw [Matrix.adjugate_apply]
  rw [heq]
  refine contDiff_matrix_det_of_entries (fun a b => ?_)
  by_cases hab : a = j
  · subst hab
    have : (fun x => ((A x).updateRow a (Pi.single i 1)) a b)
        = fun _ : 𝕏 => (Pi.single i (1 : ℝ) : n → ℝ) b := by
      funext x; rw [Matrix.updateRow_self]
    rw [this]; exact contDiff_const
  · have : (fun x => ((A x).updateRow j (Pi.single i 1)) a b) = fun x => A x a b := by
      funext x; rw [Matrix.updateRow_ne hab]
    rw [this]; exact hA a b

/-- Each entry of the inverse of an entrywise-`ContDiff` matrix family is `ContDiffAt x` when
`det (A x) ≠ 0`. -/
theorem contDiffAt_matrix_inv_entry_of_det_ne_zero {A : 𝕏 → Matrix n n ℝ}
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) {x : 𝕏}
    (hdet : (A x).det ≠ 0) (i j : n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y)⁻¹ i j) x := by
  have hentry : (fun y => (A y)⁻¹ i j)
      = fun y => (A y).det⁻¹ * (A y).adjugate i j := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [hentry]
  exact (((contDiff_matrix_det_of_entries hA).contDiffAt).inv hdet).mul
    (contDiff_matrix_adjugate_entry_of_entries hA i j).contDiffAt

/-- Entrywise `ContDiffAt` matrix multiplication. -/
theorem contDiffAt_matrix_mul_entry {mm nn pp : Type*} [Fintype nn]
    {A : 𝕏 → Matrix mm nn ℝ} {B : 𝕏 → Matrix nn pp ℝ} {x : 𝕏}
    (hA : ∀ i k, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i k) x)
    (hB : ∀ k j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => B y k j) x) (i : mm) (j : pp) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y * B y) i j) x := by
  have heq : (fun y => (A y * B y) i j) = fun y => ∑ k, A y i k * B y k j := by
    funext y; rw [Matrix.mul_apply]
  rw [heq]
  exact ContDiffAt.sum (fun k _ => (hA i k).mul (hB k j))

/-- Entrywise (global) `ContDiff` matrix multiplication. -/
theorem contDiff_matrix_mul_entry {mm nn pp : Type*} [Fintype nn]
    {A : 𝕏 → Matrix mm nn ℝ} {B : 𝕏 → Matrix nn pp ℝ}
    (hA : ∀ i k, ContDiff ℝ (⊤ : ℕ∞) (fun y => A y i k))
    (hB : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (fun y => B y k j)) (i : mm) (j : pp) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (A y * B y) i j) := by
  have heq : (fun y => (A y * B y) i j) = fun y => ∑ k, A y i k * B y k j := by
    funext y; rw [Matrix.mul_apply]
  rw [heq]
  exact ContDiff.sum (fun k _ => (hA i k).mul (hB k j))

end SchurChartC2

section SchurChartContDiff
open scoped Matrix.Norms.Elementwise
open SchurChartC2

variable {H : Fin (2 + 1) → ℕ} {r : ℕ}

/-- Each entry of the first block matrix is a `ContDiff` coordinate of `BlockParamsL2 H r`. -/
theorem contDiff_bp_fst_entry (a : Fin r ⊕ Fin (H 0 - r)) (b : Fin r ⊕ Fin (H 1 - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun P : BlockParamsL2 H r => P.1 a b) :=
  (contDiff_apply_apply (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (E := ℝ) a b).comp contDiff_fst

/-- Each entry of the second block matrix is a `ContDiff` coordinate of `BlockParamsL2 H r`. -/
theorem contDiff_bp_snd_entry (a : Fin r ⊕ Fin (H 1 - r)) (b : Fin r ⊕ Fin (H 2 - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun P : BlockParamsL2 H r => P.2 a b) :=
  (contDiff_apply_apply (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (E := ℝ) a b).comp contDiff_snd

/-- The chart domain `{det X ≠ 0} ∩ {det M11 ≠ 0}` in the block coordinates (`X = ₁₁` of the first
layer, `M11 = X S + Y Uu` the product pivot). -/
def schurChartDom (H : Fin (2 + 1) → ℕ) (r : ℕ) : Set (BlockParamsL2 H r) :=
  {P | (P.1.toBlocks₁₁).det ≠ 0 ∧
    (P.1.toBlocks₁₁ * P.2.toBlocks₁₁ + P.1.toBlocks₁₂ * P.2.toBlocks₂₁).det ≠ 0}

/-- `schurChartRaw` is `ContDiffAt ℝ ⊤` at each point of the pivot domain: every output block entry is
a `+/∗/⁻¹` combination of the `ContDiff` input coordinates, with the two pivot inverses `ContDiffAt`
where their determinants are nonzero. -/
theorem contDiffAt_schurChartRaw (P : BlockParamsL2 H r)
    (hX : (P.1.toBlocks₁₁).det ≠ 0)
    (hM11 : (P.1.toBlocks₁₁ * P.2.toBlocks₁₁ + P.1.toBlocks₁₂ * P.2.toBlocks₂₁).det ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (schurChartRaw H r) P := by
  -- `X⁻¹` entry `ContDiffAt` (det X ≠ 0).
  have hXinv : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun Q : BlockParamsL2 H r => (Q.1.toBlocks₁₁)⁻¹ a b) P := fun a b =>
    contDiffAt_matrix_inv_entry_of_det_ne_zero
      (A := fun Q : BlockParamsL2 H r => Q.1.toBlocks₁₁)
      (fun c d => contDiff_bp_fst_entry (Sum.inl c) (Sum.inl d)) hX a b
  -- `M11⁻¹` entry `ContDiffAt` (det M11 ≠ 0).
  have hMinv : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun Q : BlockParamsL2 H r =>
        (Q.1.toBlocks₁₁ * Q.2.toBlocks₁₁ + Q.1.toBlocks₁₂ * Q.2.toBlocks₂₁)⁻¹ a b) P := fun a b =>
    contDiffAt_matrix_inv_entry_of_det_ne_zero
      (A := fun Q : BlockParamsL2 H r =>
        Q.1.toBlocks₁₁ * Q.2.toBlocks₁₁ + Q.1.toBlocks₁₂ * Q.2.toBlocks₂₁)
      (fun c d => (contDiff_matrix_mul_entry
          (fun a' k' => contDiff_bp_fst_entry (Sum.inl a') (Sum.inl k'))
          (fun k' b' => contDiff_bp_snd_entry (Sum.inl k') (Sum.inl b')) c d).add
        (contDiff_matrix_mul_entry
          (fun a' k' => contDiff_bp_fst_entry (Sum.inl a') (Sum.inr k'))
          (fun k' b' => contDiff_bp_snd_entry (Sum.inr k') (Sum.inl b')) c d)) hM11 a b
  refine ContDiffAt.prodMk ?_ ?_
  · -- first output matrix `fromBlocks X Y M21 A0red`
    refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
    rcases i with i | i <;> rcases j with j | j
    · show ContDiffAt ℝ (⊤ : ℕ∞)
          (fun P : BlockParamsL2 H r => (schurChartRaw H r P).1.toBlocks₁₁ i j) P
      simp only [schurChartRaw_fst_toBlocks₁₁]
      exact (contDiff_bp_fst_entry (Sum.inl i) (Sum.inl j)).contDiffAt
    · show ContDiffAt ℝ (⊤ : ℕ∞)
          (fun P : BlockParamsL2 H r => (schurChartRaw H r P).1.toBlocks₁₂ i j) P
      simp only [schurChartRaw_fst_toBlocks₁₂]
      exact (contDiff_bp_fst_entry (Sum.inl i) (Sum.inr j)).contDiffAt
    · show ContDiffAt ℝ (⊤ : ℕ∞)
          (fun P : BlockParamsL2 H r => (schurChartRaw H r P).1.toBlocks₂₁ i j) P
      simp only [schurChartRaw_fst_toBlocks₂₁, Matrix.add_apply]
      exact (contDiffAt_matrix_mul_entry
          (fun a k => (contDiff_bp_fst_entry (Sum.inr a) (Sum.inl k)).contDiffAt)
          (fun k b => (contDiff_bp_snd_entry (Sum.inl k) (Sum.inl b)).contDiffAt) i j).add
        (contDiffAt_matrix_mul_entry
          (fun a k => (contDiff_bp_fst_entry (Sum.inr a) (Sum.inr k)).contDiffAt)
          (fun k b => (contDiff_bp_snd_entry (Sum.inr k) (Sum.inl b)).contDiffAt) i j)
    · show ContDiffAt ℝ (⊤ : ℕ∞)
          (fun P : BlockParamsL2 H r => (schurChartRaw H r P).1.toBlocks₂₂ i j) P
      simp only [schurChartRaw_fst_toBlocks₂₂, Matrix.sub_apply]
      refine ((contDiff_bp_fst_entry (Sum.inr i) (Sum.inr j)).contDiffAt).sub ?_
      exact contDiffAt_matrix_mul_entry
        (A := fun Q : BlockParamsL2 H r => Q.1.toBlocks₂₁ * Q.1.toBlocks₁₁⁻¹)
        (B := fun Q => Q.1.toBlocks₁₂)
        (fun a k => contDiffAt_matrix_mul_entry
          (fun a' k' => (contDiff_bp_fst_entry (Sum.inr a') (Sum.inl k')).contDiffAt)
          (fun k' b' => hXinv k' b') a k)
        (fun k b => (contDiff_bp_fst_entry (Sum.inl k) (Sum.inr b)).contDiffAt) i j
  · -- second output matrix `fromBlocks M11 M12 Uu A1red`
    refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
    rcases i with i | i <;> rcases j with j | j
    · show ContDiffAt ℝ (⊤ : ℕ∞)
          (fun P : BlockParamsL2 H r => (schurChartRaw H r P).2.toBlocks₁₁ i j) P
      simp only [schurChartRaw_snd_toBlocks₁₁, Matrix.add_apply]
      exact (contDiffAt_matrix_mul_entry
          (fun a k => (contDiff_bp_fst_entry (Sum.inl a) (Sum.inl k)).contDiffAt)
          (fun k b => (contDiff_bp_snd_entry (Sum.inl k) (Sum.inl b)).contDiffAt) i j).add
        (contDiffAt_matrix_mul_entry
          (fun a k => (contDiff_bp_fst_entry (Sum.inl a) (Sum.inr k)).contDiffAt)
          (fun k b => (contDiff_bp_snd_entry (Sum.inr k) (Sum.inl b)).contDiffAt) i j)
    · show ContDiffAt ℝ (⊤ : ℕ∞)
          (fun P : BlockParamsL2 H r => (schurChartRaw H r P).2.toBlocks₁₂ i j) P
      simp only [schurChartRaw_snd_toBlocks₁₂, Matrix.add_apply]
      exact (contDiffAt_matrix_mul_entry
          (fun a k => (contDiff_bp_fst_entry (Sum.inl a) (Sum.inl k)).contDiffAt)
          (fun k b => (contDiff_bp_snd_entry (Sum.inl k) (Sum.inr b)).contDiffAt) i j).add
        (contDiffAt_matrix_mul_entry
          (fun a k => (contDiff_bp_fst_entry (Sum.inl a) (Sum.inr k)).contDiffAt)
          (fun k b => (contDiff_bp_snd_entry (Sum.inr k) (Sum.inr b)).contDiffAt) i j)
    · show ContDiffAt ℝ (⊤ : ℕ∞)
          (fun P : BlockParamsL2 H r => (schurChartRaw H r P).2.toBlocks₂₁ i j) P
      simp only [schurChartRaw_snd_toBlocks₂₁]
      exact (contDiff_bp_snd_entry (Sum.inr i) (Sum.inl j)).contDiffAt
    · show ContDiffAt ℝ (⊤ : ℕ∞)
          (fun P : BlockParamsL2 H r => (schurChartRaw H r P).2.toBlocks₂₂ i j) P
      simp only [schurChartRaw_snd_toBlocks₂₂, Matrix.sub_apply]
      refine ((contDiff_bp_snd_entry (Sum.inr i) (Sum.inr j)).contDiffAt).sub ?_
      exact contDiffAt_matrix_mul_entry
        (A := fun Q : BlockParamsL2 H r =>
          Q.2.toBlocks₂₁ * (Q.1.toBlocks₁₁ * Q.2.toBlocks₁₁ + Q.1.toBlocks₁₂ * Q.2.toBlocks₂₁)⁻¹)
        (B := fun Q => Q.1.toBlocks₁₁ * Q.2.toBlocks₁₂ + Q.1.toBlocks₁₂ * Q.2.toBlocks₂₂)
        (fun a k => contDiffAt_matrix_mul_entry
          (fun a' k' => (contDiff_bp_snd_entry (Sum.inr a') (Sum.inl k')).contDiffAt)
          (fun k' b' => hMinv k' b') a k)
        (fun k b => (contDiffAt_matrix_mul_entry
          (fun a' k' => (contDiff_bp_fst_entry (Sum.inl a') (Sum.inl k')).contDiffAt)
          (fun k' b' => (contDiff_bp_snd_entry (Sum.inl k') (Sum.inr b')).contDiffAt) k b).add
          (contDiffAt_matrix_mul_entry
            (fun a' k' => (contDiff_bp_fst_entry (Sum.inl a') (Sum.inr k')).contDiffAt)
            (fun k' b' => (contDiff_bp_snd_entry (Sum.inr k') (Sum.inr b')).contDiffAt) k b)) i j

/-- **`schurChartRaw` is `ContDiffOn ℝ 2` on the pivot domain** `{det X ≠ 0} ∩ {det M11 ≠ 0}`. The
piece-2 deliverable: the explicit rational corner-elimination chart is `C²` where the two pivot
determinants are nonzero (the reduced core `A0red · A1red` and the regular corners are all rational in
`det X`, `det M11`). -/
theorem schurChartRaw_contDiffOn :
    ContDiffOn ℝ 2 (schurChartRaw H r) (schurChartDom H r) := by
  intro P hP
  obtain ⟨hX, hM11⟩ := hP
  refine ((contDiffAt_schurChartRaw P hX hM11).of_le ?_).contDiffWithinAt
  rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

end SchurChartContDiff

end DLNFibre.DLN.RLCT

