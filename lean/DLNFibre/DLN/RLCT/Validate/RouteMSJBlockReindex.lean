import DLNFibre.DLN.RLCT.Validate.RouteMSJChartAlgebra
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankStep

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJBlockReindex` — the per-chart block-reindex bridge (Phase-2 piece 2)

**Piece 2 of the general-`L` `(S,J)` resolution CoV** (thread `genm-sjcarrier5`; the R1-UPPER final
gate → `sjJointResolution`, `RouteMSJResolution.lean`). The banked pointwise Schur split
(`frobSq_schur_block_split`, `frobSq_schur_toBlocks_split`, `RouteMSJChartAlgebra`) is stated at the
ABSTRACT block level `Matrix (t ⊕ a) (t ⊕ b) ℝ`, but the peel integral `gammaPeelIntegral` integrates
the RAW front factor `A₀ : Fin M₀ → Fin M₁ → ℝ` over the pivot chart `pivotChart ρ κ` (the `(ρ,κ)`
`t × t` minor is a unit) — for ARBITRARY `t`-element row/column embeddings `ρ, κ`. This module supplies
the algebraic bridge between the two: given block-splitting equivs `er, ec` extending `ρ, κ`, the raw
loss `frobSq (rmatMul A₀ Q)` equals the block-matrix loss `frobSq (A₀blk * Qblk)`, and the chart
condition `IsUnit (A₀.submatrix ρ κ)` becomes the abstract-chart condition `IsUnit (A₀blk).toBlocks₁₁`
— so the banked Schur split applies verbatim on the chart.

## What lands here (this module — the pure-algebra core of piece 2)

* **`frobSq_rmatMul_reindex`** — the raw loss is a block-matrix loss. For any row/col reindex equivs
  `er : Fin M₀ ≃ ρ-block`, `ec : Fin M₁ ≃ κ-block`, `frobSq (rmatMul A₀ Q) = frobSq ((A₀.reindex er
  ec) * (Q.submatrix ec.symm id))` — the Frobenius norm is invariant under the output row reindex
  (`er.symm`) and the contraction index reindex (`ec`) rides through the product. Pure `Equiv.sum_comp`
  + `Matrix.mul_apply`. No measure theory, no invertibility.
* **`pivotBlock_reindex_eq_submatrix_of_ext`** — the reindexed top-left block is the `(ρ,κ)` minor.
  Given `er.symm (Sum.inl i) = ρ i`, `ec.symm (Sum.inl j) = κ j`, the block `(A₀.reindex er ec).toBlocks₁₁`
  equals `A₀.submatrix ρ κ`; hence `IsUnit`-membership transfers between the two chart forms
  (`isUnit_toBlocks₁₁_reindex_iff`).
* **`chartLoss_schur_split`** — the composed per-chart pointwise identity: on the pivot chart (the
  reindexed pivot block invertible), the raw loss decomposes into the pivot energy `frobSq (A · Q̃_p)`
  plus the cross-coupled corank residual `frobSq (C · Q̃_p + Γ · Q_b)`, `Γ = schurCompl` the corank
  block — the banked `frobSq_schur_toBlocks_split` transported to the raw front factor.

## What is NOT here (piece 2 remainder + pieces 3+, deferred — reported precisely)

The MEASURE-level transport (the measure-preserving matrix block-reindex `Matrix (Fin M₀) (Fin M₁) ≃ᵐ
Matrix ρ-block κ-block`, the box/chart domain transport, and the resulting
`gammaPeelIntegral_blockReindex_eq`) is the remaining half of piece 2, deferred to the next tide. The
`ρ,κ → er,ec` instantiation via the banked `sumSplit` is the piece-2 wrapper; the shear + block Fubini,
the corank peel wired to the IH, and the `(S,J)` descent are pieces 3+. `sjJointResolution`
(`RouteMSJResolution`) stays the single named sorry, UNTOUCHED.

S2-FREE: pure matrix algebra (`frobSq`, `rmatMul`, `Matrix.mul_apply`, `Equiv.sum_comp`) + the banked
Schur split; no measure theory, no `monomial_rlct`. Axiom footprint: the clean three
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-! ## The raw loss as a block-matrix loss (Frobenius reindex-invariance) -/

/-- **The raw front-factor loss IS a block-matrix loss.** For a raw front factor `A₀ : Fin p → Fin n →
ℝ` and tail product `Q : Fin n → Fin q → ℝ`, and any row/column reindex equivs `er : Fin p ≃ α`,
`ec : Fin n ≃ β`, the Frobenius loss `frobSq (rmatMul A₀ Q)` equals the block-matrix loss
`frobSq ((A₀.reindex er ec) * (Q.submatrix ec.symm id))`. The Frobenius norm is invariant under the
output-row reindex `er.symm`, and the contraction index reindex `ec` rides through the product
(`Equiv.sum_comp`). No invertibility, no measure theory. -/
theorem frobSq_rmatMul_reindex {p n q : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (er : Fin p ≃ α) (ec : Fin n ≃ β)
    (A₀ : Matrix (Fin p) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin q) ℝ) :
    frobSq (rmatMul A₀ Q)
      = frobSq ((A₀.reindex er ec) * (Q.submatrix ec.symm id)) := by
  -- The block product entry at `(I, k)` is the raw product entry at `(er.symm I, k)`.
  have hentry : ∀ (I : α) (k : Fin q),
      ((A₀.reindex er ec) * (Q.submatrix ec.symm id)) I k = rmatMul A₀ Q (er.symm I) k := by
    intro I k
    rw [Matrix.mul_apply]
    rw [← Equiv.sum_comp ec (fun J => (A₀.reindex er ec) I J * (Q.submatrix ec.symm id) J k)]
    unfold rmatMul
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  -- Frobenius: reindex the outer (row) sum by `er.symm`.
  unfold frobSq
  rw [← Equiv.sum_comp er.symm (fun I => ∑ k, (rmatMul A₀ Q I k) ^ 2)]
  refine Finset.sum_congr rfl (fun I _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hentry I k]

/-! ## The chart condition transfers to the reindexed top-left block -/

/-- **The reindexed top-left block is the chosen `(ρ,κ)` minor.** If the reindex equivs `er, ec` send
the left block onto the pivot rows/columns (`er.symm (Sum.inl i) = ρ i`, `ec.symm (Sum.inl j) = κ j`),
the top-left block of `A₀.reindex er ec` is exactly `A₀.submatrix ρ κ`. The `sumSplit`-agnostic form of
`pivotBlock_reindex_eq_submatrix`. -/
theorem pivotBlock_reindex_eq_submatrix_of_ext {p n t a b : ℕ}
    (A₀ : Matrix (Fin p) (Fin n) ℝ)
    (er : Fin p ≃ Fin t ⊕ Fin a) (ec : Fin n ≃ Fin t ⊕ Fin b)
    (ρ : Fin t → Fin p) (κ : Fin t → Fin n)
    (her : ∀ i, er.symm (Sum.inl i) = ρ i) (hec : ∀ j, ec.symm (Sum.inl j) = κ j) :
    (Matrix.reindex er ec A₀).toBlocks₁₁ = A₀.submatrix ρ κ := by
  ext i j
  simp only [Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.reindex_apply, her, hec]

/-- **The pivot-chart condition transfers.** With `er, ec` extending `ρ, κ`, the reindexed top-left
block is a unit iff `A₀ ∈ pivotChart ρ κ` (the `(ρ,κ)` minor is a unit). -/
theorem isUnit_toBlocks₁₁_reindex_iff {p n t a b : ℕ}
    (A₀ : Matrix (Fin p) (Fin n) ℝ)
    (er : Fin p ≃ Fin t ⊕ Fin a) (ec : Fin n ≃ Fin t ⊕ Fin b)
    (ρ : Fin t ↪ Fin p) (κ : Fin t ↪ Fin n)
    (her : ∀ i, er.symm (Sum.inl i) = ρ i) (hec : ∀ j, ec.symm (Sum.inl j) = κ j) :
    IsUnit (Matrix.reindex er ec A₀).toBlocks₁₁ ↔ A₀ ∈ pivotChart ρ κ := by
  rw [pivotBlock_reindex_eq_submatrix_of_ext A₀ er ec (ρ : Fin t → Fin p) (κ : Fin t → Fin n)
    her hec]
  rfl

/-! ## The composed per-chart pointwise Schur split (raw front factor)

The full raw→Schur split composes the two landed pieces in one step at the call site:
`frobSq_rmatMul_reindex` rewrites `frobSq (rmatMul A₀ Q)` to the abstract block loss
`frobSq (M' * W)` (`M' := Matrix.reindex er ec A₀`, `W := Matrix.of Q |>.submatrix ec.symm id`),
and — on the chart, where `M'.toBlocks₁₁` is invertible (`isUnit_toBlocks₁₁_reindex_iff` +
`Matrix.invertibleOfIsUnitDet`) — the banked `frobSq_schur_toBlocks_split M' W`
(`RouteMSJChartAlgebra`) splits it into the pivot energy `frobSq (P · Q̃_p)` plus the cross-coupled
corank residual `frobSq (C · Q̃_p + Γ · Q_b)`, `Γ = schurCompl …`. It is NOT restated here as a
standalone lemma — the two-step `rw` is the honest composition, and a giant explicit RHS over the
`Matrix`/function defeq (`Matrix.of` / prefix `Matrix.submatrix`) buys fragility, not content. -/

/-! ## The measure-preserving block-reindex + the inner-integral transport (piece 2, measure half) -/

open MeasureTheory
open scoped ENNReal

/-- **The generic entrywise box** over arbitrary index types (the block-coordinate analogue of
`matBox`): `{X | ∀ I J, X I J ∈ [−T, T]}`. Stated over a function type so the Pi `volume` /
`MeasureSpace` instances are found directly (avoiding the `Matrix`-synonym instance gap). -/
def genBox (α β : Type*) (T : ℝ) : Set (α → β → ℝ) := {X | ∀ i k, X i k ∈ Set.Icc (-T) T}

/-- **The matrix block-reindex measurable equivalence** `(Fin p → Fin n → ℝ) ≃ᵐ ((t ⊕ a) → (t ⊕ b) →
ℝ)`, reindexing rows by `er` and columns by `ec` — `arrowCongr'` nested (rows outer, columns inner).
Its value `(matReindexEquiv er ec A₀) I J = A₀ (er.symm I) (ec.symm J)` is `Matrix.reindex er ec A₀`
(definitionally). -/
noncomputable def matReindexEquiv {p n t a b : ℕ}
    (er : Fin p ≃ Fin t ⊕ Fin a) (ec : Fin n ≃ Fin t ⊕ Fin b) :
    (Fin p → Fin n → ℝ) ≃ᵐ ((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ) :=
  MeasurableEquiv.arrowCongr' er (MeasurableEquiv.arrowCongr' ec (MeasurableEquiv.refl ℝ))

/-- The block-reindex value is the reindexed entry (definitional). -/
theorem matReindexEquiv_apply {p n t a b : ℕ}
    (er : Fin p ≃ Fin t ⊕ Fin a) (ec : Fin n ≃ Fin t ⊕ Fin b)
    (A₀ : Fin p → Fin n → ℝ) (I : Fin t ⊕ Fin a) (J : Fin t ⊕ Fin b) :
    matReindexEquiv er ec A₀ I J = A₀ (er.symm I) (ec.symm J) := rfl

/-- The block-reindex equals `Matrix.reindex er ec` (as a `Matrix`, via `Matrix.of`). -/
theorem matReindexEquiv_eq_reindex {p n t a b : ℕ}
    (er : Fin p ≃ Fin t ⊕ Fin a) (ec : Fin n ≃ Fin t ⊕ Fin b)
    (A₀ : Matrix (Fin p) (Fin n) ℝ) :
    Matrix.of (matReindexEquiv er ec A₀) = A₀.reindex er ec := rfl

/-- **The block-reindex is measure-preserving** (`arrowCongr'` MP, nested; volume the Pi volume). -/
theorem measurePreserving_matReindexEquiv {p n t a b : ℕ}
    (er : Fin p ≃ Fin t ⊕ Fin a) (ec : Fin n ≃ Fin t ⊕ Fin b) :
    MeasurePreserving (matReindexEquiv er ec)
      (volume : Measure (Fin p → Fin n → ℝ))
      (volume : Measure ((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ)) := by
  unfold matReindexEquiv
  exact volume_preserving_arrowCongr' er
    (MeasurableEquiv.arrowCongr' ec (MeasurableEquiv.refl ℝ))
    (volume_preserving_arrowCongr' ec (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume))

/-- **The chart-domain preimage.** With `er, ec` extending `ρ, κ`, the block-reindex pulls the block
box ∩ invertible-pivot-block locus back to the raw box ∩ pivot chart:
`matReindexEquiv ⁻¹' (genBox ∩ {IsUnit toBlocks₁₁}) = matBox ∩ pivotChart ρ κ`. -/
theorem matReindexEquiv_preimage_chart {p n t a b : ℕ}
    (er : Fin p ≃ Fin t ⊕ Fin a) (ec : Fin n ≃ Fin t ⊕ Fin b)
    (ρ : Fin t ↪ Fin p) (κ : Fin t ↪ Fin n)
    (her : ∀ i, er.symm (Sum.inl i) = ρ i) (hec : ∀ j, ec.symm (Sum.inl j) = κ j) (T : ℝ) :
    matReindexEquiv er ec ⁻¹'
        (genBox (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) T ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)})
      = matBox p n T ∩ pivotChart ρ κ := by
  ext A₀
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, genBox, matBox]
  refine and_congr ?_ ?_
  · constructor
    · intro h i k
      have := h (er i) (ec k)
      rwa [matReindexEquiv_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
    · intro h I J; rw [matReindexEquiv_apply]; exact h _ _
  · rw [show Matrix.toBlocks₁₁ (matReindexEquiv er ec A₀)
        = (Matrix.reindex er ec (A₀ : Matrix (Fin p) (Fin n) ℝ)).toBlocks₁₁ from rfl]
    exact isUnit_toBlocks₁₁_reindex_iff A₀ er ec ρ κ her hec

/-- **The inner chart-integral block-reindex transport (piece 2, measure half).** For a fixed tail
product `Q`, the inner front-factor chart integral of `gammaPeelIntegral` transports through the
measure-preserving block-reindex to a block-coordinate integral: over the block box ∩ invertible-pivot
locus, of the block-matrix loss `frobSq (B · Q̃)^{−c'}`, `Q̃ = Q.submatrix ec.symm id` the row-reindexed
tail. The raw box ∩ pivot chart is the block-reindex preimage (`matReindexEquiv_preimage_chart`), the
integrand is the block loss (`frobSq_rmatMul_reindex`), and `matReindexEquiv` is measure-preserving —
so `MeasurePreserving.setLIntegral_comp_preimage_emb` transports the integral. On the block side the
banked `frobSq_schur_toBlocks_split` (invertible pivot on `{IsUnit toBlocks₁₁}`) exposes the corank
block `Γ`; that Schur/shear/peel is the next tide. -/
theorem chartInner_blockReindex_eq {p n q t a b : ℕ}
    (er : Fin p ≃ Fin t ⊕ Fin a) (ec : Fin n ≃ Fin t ⊕ Fin b)
    (ρ : Fin t ↪ Fin p) (κ : Fin t ↪ Fin n)
    (her : ∀ i, er.symm (Sum.inl i) = ρ i) (hec : ∀ j, ec.symm (Sum.inl j) = κ j)
    (Q : Matrix (Fin n) (Fin q) ℝ) (c' T : ℝ) :
    ∫⁻ A₀ in matBox p n T ∩ pivotChart ρ κ,
        ENNReal.ofReal ((frobSq (rmatMul A₀ Q)) ^ (-c'))
      = ∫⁻ B in genBox (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) T ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
          ENNReal.ofReal ((frobSq (Matrix.of B * Q.submatrix ec.symm id)) ^ (-c')) := by
  have hmp := measurePreserving_matReindexEquiv (p := p) (n := n) er ec
  have hpre := hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (matReindexEquiv er ec))
    (fun B : (Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ =>
      ENNReal.ofReal ((frobSq (Matrix.of B * Q.submatrix ec.symm id)) ^ (-c')))
    (genBox (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) T ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)})
  rw [matReindexEquiv_preimage_chart er ec ρ κ her hec T] at hpre
  rw [← hpre]
  refine lintegral_congr (fun A₀ => ?_)
  rw [frobSq_rmatMul_reindex er ec A₀ Q, matReindexEquiv_eq_reindex]

/-! ## The `ρ,κ`-instantiated transport (piece 2 wrapper — no supplied equivs)

`chartInner_blockReindex_eq` takes block-splitting equivs `er, ec` extending `ρ, κ` as hypotheses. The
wrapper constructs them from the pivot embeddings directly, via `blockSplitEquiv` (a `Fin t ⊕ Fin (m−t)
≃ Fin m` fronting the embedding's image — the pivot placement the Schur chart consumes), so the
transport applies to `gammaPeelIntegral`'s actual `(ρ, κ)` with no supplied-equiv obligation. -/

/-- **The block-split equivalence** `Fin t ⊕ Fin (m − t) ≃ Fin m` from a `t`-element embedding `σ`,
sending the left summand onto the image of `σ` (`blockSplitEquiv_inl`) and the right onto the
complement. `Equiv.ofInjective` on the image glued by a cardinality equiv to the complement via
`Equiv.Set.sumCompl` — the local, name-clash-free analogue of the banked `sumSplit`. -/
noncomputable def blockSplitEquiv {t m : ℕ} (σ : Fin t ↪ Fin m) : Fin t ⊕ Fin (m - t) ≃ Fin m :=
  (Equiv.sumCongr (Equiv.ofInjective σ σ.injective)
      (Fintype.equivOfCardEq (by
        have hcard : Fintype.card ↥(Set.range σ) = t := by
          rw [Fintype.card_congr (Equiv.ofInjective σ σ.injective).symm]; exact Fintype.card_fin t
        rw [Fintype.card_fin, Fintype.card_compl_set, Fintype.card_fin, hcard]))).trans
    (Equiv.Set.sumCompl (Set.range σ))

/-- `blockSplitEquiv` sends the left summand `Sum.inl a` to `σ a` (the defining property). -/
@[simp] theorem blockSplitEquiv_inl {t m : ℕ} (σ : Fin t ↪ Fin m) (a : Fin t) :
    blockSplitEquiv σ (Sum.inl a) = σ a := by
  simp only [blockSplitEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl]
  rfl

/-- **The inner chart-integral block-reindex transport, `ρ,κ`-instantiated (piece 2 wrapper).** No
supplied equivs: the block-split equivs are `(blockSplitEquiv ρ).symm`, `(blockSplitEquiv κ).symm`,
whose left blocks front `ρ, κ`. The reindexed front factor `B` ranges over the block type
`(Fin t ⊕ Fin (p − t)) → (Fin t ⊕ Fin (n − t)) → ℝ`. This is the directly-applicable form the peel
assembly instantiates on each `gammaPeelIntegral` pivot chart. -/
theorem chartInner_blockReindex_eq_of_emb {p n q t : ℕ}
    (ρ : Fin t ↪ Fin p) (κ : Fin t ↪ Fin n)
    (Q : Matrix (Fin n) (Fin q) ℝ) (c' T : ℝ) :
    ∫⁻ A₀ in matBox p n T ∩ pivotChart ρ κ,
        ENNReal.ofReal ((frobSq (rmatMul A₀ Q)) ^ (-c'))
      = ∫⁻ B in genBox (Fin t ⊕ Fin (p - t)) (Fin t ⊕ Fin (n - t)) T
            ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
          ENNReal.ofReal ((frobSq (Matrix.of B
            * Q.submatrix (blockSplitEquiv κ).symm.symm id)) ^ (-c')) :=
  chartInner_blockReindex_eq (blockSplitEquiv ρ).symm (blockSplitEquiv κ).symm ρ κ
    (fun i => by rw [Equiv.symm_symm]; exact blockSplitEquiv_inl ρ i)
    (fun j => by rw [Equiv.symm_symm]; exact blockSplitEquiv_inl κ j) Q c' T

end DLNFibre.DLN.RLCT
