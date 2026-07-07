import DLNFibre.DLN.RLCT.Validate.RouteMSJBlockReindex

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJChartWeld` — the Schur-split weld onto the block-reindex transport

**Piece 2-rest of the general-`L` `(S,J)` resolution CoV** (thread `genm-sjcarrier6`; the R1-UPPER final
gate → `sjJointResolution`, `RouteMSJResolution.lean`). Piece 2 (`RouteMSJBlockReindex`, banked)
transported the RAW front-factor chart integral (over `matBox ∩ pivotChart ρ κ`) to the block-coordinate
integral over `genBox ∩ {IsUnit toBlocks₁₁}` of the block-matrix loss `frobSq (B · Q̃)`
(`chartInner_blockReindex_eq_of_emb`). This module WELDS the banked pointwise Schur split
(`frobSq_schur_toBlocks_split`, `RouteMSJChartAlgebra`) onto that transport: on the chart — where the
pivot block `toBlocks₁₁` is a unit — the block loss `frobSq (B · Q̃)` becomes the exact cross-coupled
Schur form

    frobSq (B · Q̃) = frobSq (P · Q̃ₚ') + frobSq (C · Q̃ₚ' + Γ · Q̃_b),

    P = B.toBlocks₁₁,  C = B.toBlocks₂₁,  Γ = B.toBlocks₂₂ − C · P⁻¹ · B.toBlocks₁₂  (the corank block),
    Q̃ₚ' = Q̃.submatrix Sum.inl id + P⁻¹ · B.toBlocks₁₂ · Q̃.submatrix Sum.inr id  (the shear coordinate),
    Q̃_b = Q̃.submatrix Sum.inr id.

So the inner front-factor chart integral of `gammaPeelIntegral` equals the integral, over the SAME chart
domain, of the Schur cross-coupled form — the corank block `Γ` now EXPOSED inside the integrand. This is
the form the next tides consume: the measure-preserving shear `D ↦ Γ` (`measurePreserving_shearSub`)
frees `Γ`, and the corank-block radial peel (`corankBlock_morsePeel_lt_top`, `RouteMSJCorankPeel`)
integrates it (once the deeper core is positive — supplied by the outer `A'`-descent).

## What lands here (this module — the Schur weld)

* **`schurLoss`** — the cross-coupled Schur loss, written with `Matrix.inv` (`⁻¹`) rather than `⅟`, so it
  is a plain function of the block matrix `M'` and tail `Q` (no per-point `Invertible` instance).
* **`frobSq_schur_split_inv`** — the pointwise Schur split in `⁻¹` form: for `M'` with `IsUnit M'.toBlocks₁₁`,
  `frobSq (M' · Q) = schurLoss M' Q`. The banked `frobSq_schur_toBlocks_split` (stated with `⅟`) transported
  through `IsUnit.invertible` + `invOf_eq_nonsing_inv`.
* **`measurableSet_genBox` / `measurableSet_isUnit_toBlocks₁₁`** — the two measurability facts the chart
  integrand rewrite needs (`setLIntegral_congr_fun` on the chart domain).
* **`chartInner_schurSplit_eq`** — the abstract-block chart-integral rewrite: over `genBox ∩ {IsUnit
  toBlocks₁₁}`, `∫ frobSq (B · Q̃)^{−c'} = ∫ (schurLoss B Q̃)^{−c'}` (pointwise `frobSq_schur_split_inv`
  under `setLIntegral_congr_fun`).
* **`chartInner_schurWeld_eq_of_emb`** — the composed weld: the RAW front-factor chart integral of
  `gammaPeelIntegral`'s inner fibre equals the Schur cross-coupled block integral, for an arbitrary
  `(ρ, κ)` pivot. `chartInner_blockReindex_eq_of_emb` (transport) then `chartInner_schurSplit_eq` (split).

## What is NOT here (the standing mountain — reported precisely)

The Schur form is EXPOSED but not yet INTEGRATED. What remains for later tides (the ~65–75% genuinely-new
construction, decorrelated-Codex-scoped): (i) the measure-preserving shear `D ↦ Γ` decomposing the `genBox`
integral over the `(P, B₁₂, C, Γ)` block coordinates; (ii) the corank-block radial peel of `Γ`
(`corankBlock_morsePeel_lt_top`) — which needs the deeper core strictly positive (`w > 0`), supplied by
the OUTER tail-parameter `A'`-integral; (iii) the `(S,J)` `Nat`-measure descent of that outer integral to
the monomial terminal (`sjLoss_terminal_lintegral_lt_top`), wiring the reduced coupling to the strong IH
(`redChain t M`). `sjJointResolution` (`RouteMSJResolution`) stays the single named sorry, UNTOUCHED — this
tide adds a sorry-free module.

S2-FREE: matrix algebra (`frobSq_schur_toBlocks_split`, `Matrix.det` continuity) + measure-preserving
block-reindex (via `chartInner_blockReindex_eq_of_emb`); no `monomial_rlct`. Axiom footprint: the clean
three `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## The cross-coupled Schur loss (in `⁻¹` form) -/

/-- **The cross-coupled Schur loss** of a block-indexed front factor `M'` against a tail `Q`, written
with `Matrix.inv` (`⁻¹`) so it is a plain function of `M'` (no `Invertible` instance): the pivot energy
`frobSq (P · Q̃ₚ')` plus the corank energy `frobSq (C · Q̃ₚ' + Γ · Q_b)`, `P = M'.toBlocks₁₁`,
`C = M'.toBlocks₂₁`, `Γ = M'.toBlocks₂₂ − C·P⁻¹·M'.toBlocks₁₂`, `Q̃ₚ' = Qₚ + P⁻¹·M'.toBlocks₁₂·Q_b`. On the
chart (`IsUnit P`) this equals `frobSq (M' · Q)` (`frobSq_schur_split_inv`). -/
noncomputable def schurLoss {t a b q : ℕ}
    (M' : Matrix (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) ℝ) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) : ℝ :=
  frobSq (M'.toBlocks₁₁ *
      (Q.submatrix Sum.inl id + M'.toBlocks₁₁⁻¹ * M'.toBlocks₁₂ * Q.submatrix Sum.inr id))
    + frobSq (M'.toBlocks₂₁ *
        (Q.submatrix Sum.inl id + M'.toBlocks₁₁⁻¹ * M'.toBlocks₁₂ * Q.submatrix Sum.inr id)
      + (M'.toBlocks₂₂ - M'.toBlocks₂₁ * M'.toBlocks₁₁⁻¹ * M'.toBlocks₁₂) * Q.submatrix Sum.inr id)

/-- **The pointwise Schur split in `⁻¹` form.** For a block-indexed front factor `M'` whose pivot block
`M'.toBlocks₁₁` is a unit, the block loss `frobSq (M' · Q)` equals the cross-coupled Schur loss
`schurLoss M' Q`. The banked `frobSq_schur_toBlocks_split` (stated with `⅟`, `[Invertible]`) via
`IsUnit.invertible` (the instance) + `invOf_eq_nonsing_inv` (`⅟ = ⁻¹`) + unfolding `schurCompl`. -/
theorem frobSq_schur_split_inv {t a b q : ℕ}
    (M' : Matrix (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) ℝ) (hU : IsUnit M'.toBlocks₁₁)
    (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) :
    frobSq (M' * Q) = schurLoss M' Q := by
  haveI : Invertible M'.toBlocks₁₁ := hU.invertible
  rw [frobSq_schur_toBlocks_split M' Q, schurLoss]
  simp only [schurCompl, invOf_eq_nonsing_inv]

/-! ## Measurability of the chart domain -/

/-- **The generic entrywise box is measurable.** `genBox α β T` (over finite index types) is the finite
intersection over `(i, k)` of the preimages `{X | X i k ∈ [−T, T]}` — each a measurable preimage of `Icc`
under the coordinate evaluation. -/
theorem measurableSet_genBox {α β : Type*} [Finite α] [Finite β] (T : ℝ) :
    MeasurableSet (genBox α β T) := by
  have hset : genBox α β T
      = ⋂ (i : α), ⋂ (k : β), {X : α → β → ℝ | X i k ∈ Set.Icc (-T) T} := by
    ext X; simp only [genBox, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun k => ?_))
  exact ((measurable_pi_apply k).comp (measurable_pi_apply i)) measurableSet_Icc

/-- **The invertible-pivot-block locus is measurable.** `{B | IsUnit B.toBlocks₁₁}` is the preimage of
`{0}ᶜ` under the continuous map `B ↦ det B.toBlocks₁₁` (`Matrix.isUnit_iff_isUnit_det` + `isUnit_iff_ne_zero`
over the field `ℝ`; the block determinant is a polynomial in the entries, hence continuous). -/
theorem measurableSet_isUnit_toBlocks₁₁ {t a b : ℕ} :
    MeasurableSet {B : (Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ | IsUnit (Matrix.toBlocks₁₁ B)} := by
  have hdet : Measurable (fun B : (Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ =>
      (Matrix.toBlocks₁₁ B).det) := by
    refine (Continuous.matrix_det ?_).measurable
    refine continuous_matrix (fun i j => ?_)
    exact (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))
  have hEq : {B : (Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ | IsUnit (Matrix.toBlocks₁₁ B)}
      = {B | (Matrix.toBlocks₁₁ B).det ≠ 0} := by
    ext B
    exact (Matrix.isUnit_iff_isUnit_det _).trans isUnit_iff_ne_zero
  rw [hEq]
  exact hdet (measurableSet_singleton (0 : ℝ)).compl

/-! ## The Schur-split chart-integral rewrite (abstract block level) -/

/-- **The Schur-split chart-integral rewrite (abstract block level).** Over the chart domain
`genBox ∩ {IsUnit toBlocks₁₁}`, the block-matrix loss integral `∫ frobSq (B · Q̃)^{−c'}` equals the
cross-coupled Schur loss integral `∫ (schurLoss B Q̃)^{−c'}`: on the chart the pivot block is a unit, so
`frobSq_schur_split_inv` applies pointwise (`setLIntegral_congr_fun` on the measurable chart domain). -/
theorem chartInner_schurSplit_eq {t a b q : ℕ}
    (Qt : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (c' T : ℝ) :
    ∫⁻ B in genBox (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) T ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
        ENNReal.ofReal ((frobSq (Matrix.of B * Qt)) ^ (-c'))
      = ∫⁻ B in genBox (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) T ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
          ENNReal.ofReal ((schurLoss (Matrix.of B) Qt) ^ (-c')) := by
  refine setLIntegral_congr_fun
    ((measurableSet_genBox T).inter measurableSet_isUnit_toBlocks₁₁) (fun B hB => ?_)
  rw [frobSq_schur_split_inv (Matrix.of B) hB.2 Qt]

/-! ## The composed weld — the RAW chart integral IS the Schur cross-coupled block integral -/

/-- **The Schur-split weld onto the block-reindex transport (piece 2-rest).** For an arbitrary
`t`-element `(ρ, κ)` pivot and a fixed tail product `Q`, the RAW front-factor chart integral (the inner
fibre of `gammaPeelIntegral`) equals the cross-coupled Schur block integral over `genBox ∩ {IsUnit
toBlocks₁₁}` — the corank block `Γ = B.toBlocks₂₂ − B.toBlocks₂₁·(B.toBlocks₁₁)⁻¹·B.toBlocks₁₂` now
EXPOSED inside the integrand `schurLoss (Matrix.of B) Q̃`, `Q̃ = Q.submatrix (blockSplitEquiv κ) id` the
row-reindexed tail. Composes the banked block-reindex transport
(`chartInner_blockReindex_eq_of_emb`) with the pointwise Schur split (`chartInner_schurSplit_eq`). This
is the algebraic bridge the general-`L` `(S,J)` peel welds: the freed `Γ` is what the shear + corank
radial peel integrate. -/
theorem chartInner_schurWeld_eq_of_emb {p n q t : ℕ}
    (ρ : Fin t ↪ Fin p) (κ : Fin t ↪ Fin n)
    (Q : Matrix (Fin n) (Fin q) ℝ) (c' T : ℝ) :
    ∫⁻ A₀ in matBox p n T ∩ pivotChart ρ κ,
        ENNReal.ofReal ((frobSq (rmatMul A₀ Q)) ^ (-c'))
      = ∫⁻ B in genBox (Fin t ⊕ Fin (p - t)) (Fin t ⊕ Fin (n - t)) T
            ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
          ENNReal.ofReal
            ((schurLoss (Matrix.of B) (Q.submatrix (blockSplitEquiv κ).symm.symm id)) ^ (-c')) := by
  rw [chartInner_blockReindex_eq_of_emb ρ κ Q c' T]
  exact chartInner_schurSplit_eq (Q.submatrix (blockSplitEquiv κ).symm.symm id) c' T

end DLNFibre.DLN.RLCT
