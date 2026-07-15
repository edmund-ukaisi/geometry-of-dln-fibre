import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankSurvival
import DLNFibre.DLN.RLCT.Validate.RouteMSJUnitsBridge
import Mathlib.MeasureTheory.Measure.Prod

set_option linter.style.longLine false

/-!
# `RouteMSJCorankGeneric` — the generic corank-Gram PosDef discharge (hGae, part (c))

**Thread `genm-sj5-capstone` (aoyagi-full Stage 2), the rankgen hGae-discharge chain.** The joint
`(z, A_cor)` corank-Gram positivity `hGae` the coupled-incidence route (`shellSpine_le_frontCharge`)
threads: `(Q_b · Q_bᵀ).PosDef` a.e. in `p = (z, A_cor)`, `Q_b = A_cor · Z_deep(z)`.

The discharge chain (rankgen cert, `genm-rankgen`):
`b ≤ deepTailMin M` (`tailWidth_le_deepTailMin_of_binding`, banked)
→ (c1) `∀ᵐ z, deepTailMin M ≤ rank (deeperFlagZdeep M u z)` — the deep-factor generic rank (the ONE new
  content, the min-minor-of-product nonvanishing rankgen flagged; **NOT built here — an input hypothesis
  `hZrank`**, the isolated AG-direction piece the route otherwise avoids)
→ (c2) per-`z`: `b ≤ rank Z_deep → ∀ᵐ A_cor, (Q_b · Q_bᵀ).PosDef` (`corank_survival_ae` giving
  `rank(A·Z) = b`, then `posDef_gram_of_rank_eq`) — **`corank_gram_posDef_ae`, landed here**
→ (c3) the product-a.e. combine `∀ᵐ z, ∀ᵐ A_cor → ∀ᵐ (z, A_cor)` — **`hGae_from_deepRank`, landed here**.

So this file lands (c2)+(c3): `hGae` REDUCED to the deep-factor generic rank `hZrank` (c1). Network-free
+ measure theory; sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal

/-- **(c2) — the corank Gram is PosDef a.e. in the free block.** For a fixed deep factor `Zdeep` of rank
`≥ b`, a.e. free `A : Fin b → Fin m → ℝ` gives a POSITIVE DEFINITE corank Gram
`(A · Zdeep)(A · Zdeep)ᵀ`. Composes the banked `corank_survival_ae` (`rank (A·Zdeep) = b` a.e.) with
`posDef_gram_of_rank_eq` (full row rank ⟹ Gram PosDef). -/
theorem corank_gram_posDef_ae {b m D : ℕ} (Zdeep : Matrix (Fin m) (Fin D) ℝ) (hb : b ≤ Zdeep.rank) :
    ∀ᵐ A : Fin b → Fin m → ℝ,
      ((Matrix.of A * Zdeep) * (Matrix.of A * Zdeep)ᵀ).PosDef := by
  filter_upwards [corank_survival_ae Zdeep hb] with A hA
  exact posDef_gram_of_rank_eq (Matrix.of A * Zdeep) hA

/-- The corank row-block of `hsQ` is the deep-factor product `A_cor · Zf z`
(`(fromRows _ (of A_cor · Zf z)).submatrix Sum.inr id`). -/
theorem hsQ_submatrix_inr {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (z : Params (redChain u M))
    (A_cor : Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) :
    (hsQ M u Zf z A_cor).submatrix Sum.inr id = Matrix.of A_cor * Zf z := by
  ext i j
  simp only [hsQ, Matrix.submatrix_apply, id_eq, Matrix.fromRows_apply_inr]

/-- **(c3) — the joint corank-Gram PosDef `hGae` from the deep-factor generic rank.** Given the
deep-factor generic rank `hZrank : ∀ᵐ z, b ≤ rank (deeperFlagZdeep M u z)` (the (c1) input — the
min-minor-of-product nonvanishing rankgen certified; the AG-direction piece not built here), the coupled
corank Gram `(Q_b · Q_bᵀ)` is positive definite a.e. in the JOINT `p = (z, A_cor)`,
`Q_b = A_cor · deeperFlagZdeep M u z` (`= (hsQ …).submatrix Sum.inr id`). This is the exact `hGae` the
coupled-incidence route (`shellSpine_le_frontCharge`) threads.

Product-a.e. combine: transport the box measure to `(vol.restrict paramsBox).prod (vol.restrict matBox)`
(`Measure.volume_eq_prod` + `Measure.prod_restrict`); `ae_prod_iff_ae_ae` on the measurable good set
`{p | IsUnit (Q_b·Q_bᵀ)}` (= `{det ≠ 0}`) reduces to fiberwise `∀ᵐ z, ∀ᵐ A_cor, IsUnit`, discharged by
`hZrank` + `corank_gram_posDef_ae` (`.isUnit`); then `PosSemidef.posDef_iff_isUnit` (`Q_b·Q_bᵀ` PSD) turns
`IsUnit` back into `PosDef`. -/
theorem hGae_from_deepRank {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hZrank : ∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain u M) 1)),
        M 1 - u ≤ (deeperFlagZdeep M u z).rank) :
    ∀ᵐ p ∂(volume.restrict (paramsBoxM (redChain u M) 1
        ×ˢ matBox (M 1 - u) (M 2) 1)),
      ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
        * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).PosDef := by
  classical
  set Zf := deeperFlagZdeep M u with hZf
  -- deep factor measurable (the `deeperFlag_spineToCore` pattern)
  have hproj : Measurable (fun z : Params (redChain u M) =>
      (paramsHeadSplit (redChain u M) z).2) :=
    measurable_snd.comp (paramsHeadSplit (redChain u M)).measurable
  have hZdeepMeas : Measurable Zf :=
    measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun jj =>
      ((continuous_prod (dropHead (redChain u M))).matrix_elem i jj).measurable.comp hproj))
  -- the corank Gram entries, measurable over the RAW pi type (dodging the Matrix diamond); the `hsQ`
  -- form is used throughout — its width types unify, unlike the raw `of p.2 * Zf p.1` product.
  have hGramraw : Measurable (fun p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ) =>
      (fun i j => (((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)
          * ((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)ᵀ) i j
        : Fin (M 1 - u) → Fin (M 1 - u) → ℝ)) := by
    rw [measurable_pi_iff]; intro i; rw [measurable_pi_iff]; intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq,
      hsQ, Matrix.fromRows_apply_inr, Matrix.of_apply]
    refine Finset.measurable_sum _ (fun l _ =>
      (Finset.measurable_sum _ (fun k _ => ?_)).mul (Finset.measurable_sum _ (fun k _ => ?_)))
    · exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp (hZdeepMeas.comp measurable_fst)))
    · exact ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp measurable_snd)).mul
        ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp (hZdeepMeas.comp measurable_fst)))
  -- the good set `{p | IsUnit (Q_b Q_bᵀ)}` is measurable (`= {det ≠ 0}`)
  have hof : Continuous (Matrix.of :
      (Fin (M 1 - u) → Fin (M 1 - u) → ℝ) → Matrix (Fin (M 1 - u)) (Fin (M 1 - u)) ℝ) := continuous_id
  have hdetmeas : Measurable (fun p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ) =>
      (((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)
        * ((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)ᵀ).det) :=
    (Continuous.matrix_det hof).measurable.comp hGramraw
  have hmeasSet : MeasurableSet {p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ) |
      IsUnit (((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)
        * ((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)ᵀ)} := by
    have hEq : {p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ) |
          IsUnit (((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)
            * ((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)ᵀ)}
        = {p | (((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)
            * ((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)ᵀ).det ≠ 0} := by
      ext p
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    rw [hEq]; exact hdetmeas (measurableSet_singleton (0 : ℝ)).compl
  -- transport the box measure to a product; combine fiberwise
  rw [Measure.volume_eq_prod (Params (redChain u M)) (Fin (M 1 - u) → Fin (M 2) → ℝ),
    ← Measure.prod_restrict]
  have hunit : ∀ᵐ p ∂((volume.restrict (paramsBoxM (redChain u M) 1)).prod
        (volume.restrict (matBox (M 1 - u) (M 2) 1))),
      IsUnit (((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)
        * ((hsQ M u Zf p.1 p.2).submatrix Sum.inr id)ᵀ) := by
    rw [Measure.ae_prod_iff_ae_ae hmeasSet]
    filter_upwards [hZrank] with z hz
    filter_upwards [ae_restrict_of_ae (corank_gram_posDef_ae (Zf z) hz)] with A hA
    rw [hsQ_submatrix_inr]
    exact hA.isUnit
  filter_upwards [hunit] with p hp
  exact ((posSemidef_mul_transpose _).posDef_iff_isUnit).mpr hp

end DLNFibre.DLN.RLCT
