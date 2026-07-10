import DLNFibre.DLN.RLCT.Validate.RouteMSJGoodChart

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDepthReduce` — the depth reduction (gap A)

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain.** This is the pointwise algebraic core the
change-of-variables consumes to identify the *freed* Schur loss with the good-chart cross-
coupled loss `g_cc`.

After the banked measure-side entry `chartInner_eq_outerShearFree` (`RouteMSJGoodChart`), the inner
fibre of `gammaPeelIntegral` is an outer/inner integral of `(freedSchurLoss x Γ Q̃)^{−c'}`,
`Q̃ = Q.submatrix (blockSplitEquiv κ) id`, `Q = prod (tailChain M) A'`. The endpoint
`sjGoodMap_loss_matBox_lt_top` is stated via the good-chart map `sjGoodMap`. This module bridges the
two integrands: it shows that **once both row-blocks of `Q̃` factor through a common deep
factor `A₂` (the depth reduction), `freedSchurLoss = g_cc`.**

* **`freedSchurLoss_eq_sjGoodMap`** — the hypothesis form. GIVEN the sheared pivot rows
  `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b = v·A₂` and the corank rows `Q_b = W·A₂`, the freed Schur loss equals the
  cross-coupled loss `g_cc(Γ, v) = frobSq(P·v·A₂) + frobSq((C·v + Γ·W)·A₂)`. Composes the banked
  `schurSplitLoss_eq_sjGoodMap` after substituting the two factorizations.
* **`freedSchurLoss_eq_sjGoodMap_mul`** — the product form. From a two-block factorization
  `Q̃ = Ã₁ · A₂` of the (row-reindexed) tail product, the depth-reduction data is read off directly:
  `W = (Ã₁)_b` (the corank rows of the front factor), `v = (Ã₁)_p + P⁻¹·B₁₂·(Ã₁)_b`. The row-block
  submatrices distribute over the product (`Matrix.submatrix_mul`), delivering `hp`/`hb`.

This is item 4's algebraic core (statement card `genm-resmap`, "the deferred analytic core"); the
front factor `Ã₁ = (A' 0).submatrix (blockSplitEquiv κ) id` and deep factor `A₂ = reindex (prod …)`
come from
the banked front-peel `prod_front_peel` (`RouteMFrontPeel`), composed in the assembly.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis, no measure
theory).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-- **The depth reduction (hypothesis form).** For the outer block triple `x = (P, B₁₂, C)`, a free
corank block `Γ`, and a tail product `Q` whose row-blocks factor through a common deep factor `A₂`
— the sheared pivot rows `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b = v·A₂` (`hp`), the corank rows `Q_b = W·A₂`
(`hb`) — the freed Schur loss equals the good-chart cross-coupled loss `g_cc(Γ, v)`:
`freedSchurLoss x Γ Q = frobSq(P·v·A₂) + frobSq((C·v + Γ·W)·A₂)`. Substitute `hp`, `hb` into the two
Schur energies, then the banked `schurSplitLoss_eq_sjGoodMap`. -/
theorem freedSchurLoss_eq_sjGoodMap {t a b h o : ℕ}
    (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (Q : Matrix (Fin t ⊕ Fin b) (Fin o) ℝ)
    (v : Matrix (Fin t) (Fin h) ℝ) (W : Matrix (Fin b) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ)
    (hp : Q.submatrix Sum.inl id + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id
      = v * A2)
    (hb : Q.submatrix Sum.inr id = W * A2) :
    freedSchurLoss x Γ Q
      = frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) W A2 (Matrix.of Γ, v)).1
        + frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) W A2 (Matrix.of Γ, v)).2 := by
  unfold freedSchurLoss
  rw [hp, hb]
  exact schurSplitLoss_eq_sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) (Matrix.of Γ) W A2 v

/-- **The depth reduction (product form).** From a two-block factorization `Q̃ = Ã₁ · A₂` of the
row-reindexed tail product, the depth-reduction data reads off directly: the corank map is the
corank rows of the front factor `W := (Ã₁)_b = Ã₁.submatrix Sum.inr id`, the boundary rows
are `v := (Ã₁)_p + P⁻¹·B₁₂·(Ã₁)_b`. The row-block submatrices distribute over the product
(`Matrix.submatrix_mul` with the bijective identity middle reindex), delivering `hp`/`hb` for
`freedSchurLoss_eq_sjGoodMap`. This is the form the CoV assembly consumes after the banked
front-peel exposes `Ã₁` and `A₂`. -/
theorem freedSchurLoss_eq_sjGoodMap_mul {t a b h o : ℕ}
    (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (A1 : Matrix (Fin t ⊕ Fin b) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) :
    freedSchurLoss x Γ (A1 * A2)
      = frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) (A1.submatrix Sum.inr id) A2
          (Matrix.of Γ, A1.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * A1.submatrix Sum.inr id)).1
        + frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) (A1.submatrix Sum.inr id) A2
          (Matrix.of Γ, A1.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * A1.submatrix Sum.inr id)).2 := by
  -- row-block submatrices distribute over the product (bijective identity middle reindex).
  have hrowl : (A1 * A2).submatrix (Sum.inl : Fin t → Fin t ⊕ Fin b) id
      = A1.submatrix Sum.inl id * A2 := by
    rw [Matrix.submatrix_mul A1 A2 Sum.inl id id Function.bijective_id, Matrix.submatrix_id_id]
  have hrowr : (A1 * A2).submatrix (Sum.inr : Fin b → Fin t ⊕ Fin b) id
      = A1.submatrix Sum.inr id * A2 := by
    rw [Matrix.submatrix_mul A1 A2 Sum.inr id id Function.bijective_id, Matrix.submatrix_id_id]
  refine freedSchurLoss_eq_sjGoodMap x Γ (A1 * A2) _ _ A2 ?_ hrowr
  -- `hp`: the sheared pivot rows factor as `v · A₂`.
  rw [hrowl, hrowr, Matrix.add_mul, ← Matrix.mul_assoc]

end DLNFibre.DLN.RLCT
