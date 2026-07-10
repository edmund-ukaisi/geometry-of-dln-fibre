import DLNFibre.DLN.RLCT.Validate.RouteMSJFreedPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSJDepthReduce

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGoodCoords` — gammaPeelIntegral in good-chart coordinates

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain.** Composes the banked measure-side entry
`gammaPeelIntegral_schurShearFree_eq` (`RouteMSJFreedPeel`) with the banked front-peel
`prod_front_peel` (`RouteMFrontPeel`) and the depth reduction `freedSchurLoss_eq_sjGoodMap_mul`
(`RouteMSJDepthReduce`, gap A) to rewrite `gammaPeelIntegral` — as an EQUALITY, unconditionally —
into the good-chart cross-coupled loss `g_cc` coordinates.

* **`sjTail_factor`** — the two-block factorization of the row-reindexed tail product: for any tail
  parameter `A'`, `(prod (tailChain M) A').submatrix (blockSplitEquiv κ) id = Ã₁ · A₂`, front factor
  `Ã₁ = (A' 0).submatrix (blockSplitEquiv κ) id`, deep factor `A₂` the banked front-peel remainder.
  Front-peel (`prod_front_peel`) + the row-block submatrix distributing over the product
  (`Matrix.submatrix_mul`, bijective identity middle reindex).
* **`gammaPeelIntegral_sjGoodMap_eq`** — the EQUALITY: `gammaPeelIntegral M t ρ κ c'` equals the
  triple integral (outer tail box `A'`, outer domain `x`, freed corank block `Γ`) of the good-chart
  cross-coupled loss `(frobSq (sjGoodMap …).1 + frobSq (sjGoodMap …).2)^{−c'}`, good-chart data
  read off from `(A', x)`: `P = of x.1.1`, `C = of x.2`, `W = (Ã₁)_b`, `A₂` the deep factor,
  `v = (Ã₁)_p + P⁻¹·B₁₂·(Ã₁)_b`. No hypotheses, no finiteness — the integrand-level bridge from the
  measure-side entry to the endpoint's `sjGoodMap`-loss shape.

The remaining un-banked content is the FINITENESS of this triple integral: the `v`-exposure CoV (the
pivot rows `(Ã₁)_p ↦ v` translation) + the endpoint `sjGoodMap_loss_matBox_lt_top` + the environment
integration on the refined (good ∪ deeper) cover with the `(S,J)` L-recursion. This module does not
touch `sjJointResolution` (`RouteMSJResolution`); it is the sorry-free coordinate bridge the descent
consumes.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (measure-preserving CoV, banked, + matrix
algebra; no analysis beyond the banked corner endpoint's absence here).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

variable {L : ℕ}

/-- **The two-block factorization of the row-reindexed tail product.** For any tail parameter `A'`,
the `(ρ,κ)`-row-reindexed full tail product factors as the reindexed leading layer times the banked
front-peel remainder: `(prod (tailChain M) A').submatrix (blockSplitEquiv κ) id = Ã₁ · A₂`, with
front factor `Ã₁ = (A' 0).submatrix (blockSplitEquiv κ) id`. Front-peel (`prod_front_peel`) exposes
`prod = (A' 0) · A₂`; the row-block submatrix distributes over the product left factor
(`Matrix.submatrix_mul`, bijective identity middle reindex). -/
theorem sjTail_factor (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (κ : Fin t ↪ Fin (M 1))
    (A' : Params (tailChain M)) :
    ∃ A2 : Matrix (Fin ((tailChain M) ((0 : Fin (L + 1)).succ)))
        (Fin ((tailChain M) (Fin.last (L + 1)))) ℝ,
      (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id
        = ((A' 0).submatrix (blockSplitEquiv κ) id) * A2 := by
  have emid : Mtail (tailChain M) (0 : Fin (L + 1)) = (tailChain M) ((0 : Fin (L + 1)).succ) := rfl
  have ecol : Mtail (tailChain M) (Fin.last L) = (tailChain M) (Fin.last (L + 1)) := rfl
  set Ad := Matrix.reindex (finCongr emid) (finCongr ecol)
      (prod (Mtail (tailChain M)) (Atail (tailChain M) A')) with hAd
  refine ⟨Ad, ?_⟩
  rw [prod_front_peel (tailChain M) A' emid ecol, ← hAd]
  refine (Matrix.submatrix_mul (A' 0) Ad (blockSplitEquiv κ) id id Function.bijective_id).trans ?_
  rw [Matrix.submatrix_id_id]

/-- **The good-chart cross-coupled loss in tail coordinates** `g_cc` — the endpoint's
read off from a two-block tail factorization `Ã₁ · A₂`: `frobSq (P·v·A₂) + frobSq ((C·v + Γ·W)·A₂)`,
`P = of x.1.1`, `C = of x.2`, `W = (Ã₁)_b`, `v = (Ã₁)_p + P⁻¹·B₁₂·(Ã₁)_b`. Definitionally equal to
`freedSchurLoss x Γ (Ã₁ · A₂)` (gap A `freedSchurLoss_eq_sjGoodMap_mul`); it names the endpoint
shape `sjGoodMap_loss_matBox_lt_top` consumes. -/
noncomputable def sjGoodChartLoss {t a b h o : ℕ} (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (A1 : Matrix (Fin t ⊕ Fin b) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) : ℝ :=
  frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) (A1.submatrix Sum.inr id) A2
      (Matrix.of Γ,
        A1.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * A1.submatrix Sum.inr id)).1
    + frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) (A1.submatrix Sum.inr id) A2
      (Matrix.of Γ,
        A1.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * A1.submatrix Sum.inr id)).2

/-- `sjGoodChartLoss` is the good-chart form of the freed Schur loss on a product tail (gap A). -/
theorem freedSchurLoss_eq_sjGoodChartLoss {t a b h o : ℕ} (x : SJOuter t a b)
    (Γ : Fin a → Fin b → ℝ) (A1 : Matrix (Fin t ⊕ Fin b) (Fin h) ℝ)
    (A2 : Matrix (Fin h) (Fin o) ℝ) :
    freedSchurLoss x Γ (A1 * A2) = sjGoodChartLoss x Γ A1 A2 :=
  freedSchurLoss_eq_sjGoodMap_mul x Γ A1 A2

/-- **`gammaPeelIntegral` in good-chart `g_cc` coordinates (EQUALITY).** For any pivot cut
`(t, ρ, κ)`, `gammaPeelIntegral M t ρ κ c'` equals the freed triple integral of the cross-coupled
loss `sjGoodChartLoss x Γ Ã₁ A₂` — outer over the tail box `A'`, then the outer domain `x`, then
the freed corank block `Γ` — front factor `Ã₁ = (A' 0).submatrix (blockSplitEquiv κ) id`, deep
factor `A₂` the front-peel remainder (`sjTail_factor`). Composes the banked measure-side entry
`gammaPeelIntegral_schurShearFree_eq` with the pointwise integrand rewrite (`sjTail_factor` for the
factorization, `freedSchurLoss_eq_sjGoodChartLoss`/gap A for the loss identification) under
`lintegral_congr`. No hypotheses, no finiteness — the integrand-level bridge from the measure-side
to the endpoint's `sjGoodMap`-loss shape. -/
theorem gammaPeelIntegral_sjGoodMap_eq (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      = ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
            ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
                Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
              ENNReal.ofReal
                ((sjGoodChartLoss x Γ ((A' 0).submatrix (blockSplitEquiv κ) id)
                    (Classical.choose (sjTail_factor M t κ A'))) ^ (-c')) := by
  rw [gammaPeelIntegral_schurShearFree_eq M t ρ κ c']
  refine lintegral_congr (fun A' => lintegral_congr (fun x => lintegral_congr (fun Γ => ?_)))
  have heq : freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)
      = sjGoodChartLoss x Γ ((A' 0).submatrix (blockSplitEquiv κ) id)
          (Classical.choose (sjTail_factor M t κ A')) := by
    rw [← freedSchurLoss_eq_sjGoodChartLoss]
    congr 1
    exact Classical.choose_spec (sjTail_factor M t κ A')
  rw [heq]

end DLNFibre.DLN.RLCT
