import DLNFibre.DLN.RLCT.Validate.RouteMSJGoodCoords

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDeepFactor` — the explicit deep factor (Classical.choose-free)

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain, transport prerequisite.** The measure-side
`gammaPeelIntegral_sjGoodMap_eq` (`RouteMSJGoodCoords`) carries the two-block deep factor as
`Classical.choose (sjTail_factor …)` — opaque, and its statement mentions the abstracted term, so it
blocks the `rw`/motive the measure transport needs. This module names the deep factor EXPLICITLY as
`sjDeepFactor M A'` (the banked front-peel remainder), reproves the factorization and the
equality with it, and — the key fact for the transport — shows `sjDeepFactor` depends on the tail
parameter `A'` only through the DEEPER layers (`A' 1, …, A' L`), NOT the leading layer `A' 0`. This
exactly what lets the `A' 0`-vs-deeper Pi-split treat the deep factor as constant in `A' 0`.

* **`sjDeepFactor M A'`** — the explicit deep factor `reindex (prod (Mtail (tailChain M))
  (Atail (tailChain M) A'))` (the leading-layer front-peel remainder).
* **`sjTail_factor_explicit`** — the factorization with the explicit witness: `(prod (tailChain M)
  A').submatrix (blockSplitEquiv κ) id = Ã₁ · sjDeepFactor M A'`.
* **`sjDeepFactor_update_zero`** — the `A' 0`-independence: `sjDeepFactor M (update A' 0 B) =
  sjDeepFactor M A'` (the deep factor reads only the tail-of-tail).
* **`gammaPeelIntegral_sjGoodMap_eq'`** — the measure-side equality with the explicit deep factor
  (Classical.choose-free), ready for the Pi-split.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

variable {L : ℕ}

/-- **The explicit deep factor** — the leading-layer front-peel remainder `reindex (prod
(Mtail (tailChain M)) (Atail (tailChain M) A'))`, a function of the DEEPER tail layers only. The
`Classical.choose (sjTail_factor …)` witness made explicit. -/
noncomputable def sjDeepFactor (M : Fin (L + 1 + 1 + 1) → ℕ) (A' : Params (tailChain M)) :
    Matrix (Fin ((tailChain M) ((0 : Fin (L + 1)).succ)))
      (Fin ((tailChain M) (Fin.last (L + 1)))) ℝ :=
  Matrix.reindex
    (finCongr (show Mtail (tailChain M) (0 : Fin (L + 1))
      = (tailChain M) ((0 : Fin (L + 1)).succ) from rfl))
    (finCongr (show Mtail (tailChain M) (Fin.last L)
      = (tailChain M) (Fin.last (L + 1)) from rfl))
    (prod (Mtail (tailChain M)) (Atail (tailChain M) A'))

/-- **The factorization with the explicit deep factor.** `(prod (tailChain M) A').submatrix
(blockSplitEquiv κ) id = Ã₁ · sjDeepFactor M A'`, `Ã₁ = (A' 0).submatrix (blockSplitEquiv κ) id`.
Same proof as `sjTail_factor` (front-peel + `Matrix.submatrix_mul` via a fully-applied `.trans`),
the explicit witness. -/
theorem sjTail_factor_explicit (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (κ : Fin t ↪ Fin (M 1))
    (A' : Params (tailChain M)) :
    (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id
      = ((A' 0).submatrix (blockSplitEquiv κ) id) * sjDeepFactor M A' := by
  have emid : Mtail (tailChain M) (0 : Fin (L + 1)) = (tailChain M) ((0 : Fin (L + 1)).succ) := rfl
  have ecol : Mtail (tailChain M) (Fin.last L) = (tailChain M) (Fin.last (L + 1)) := rfl
  rw [prod_front_peel (tailChain M) A' emid ecol]
  refine (Matrix.submatrix_mul (A' 0) (sjDeepFactor M A') (blockSplitEquiv κ) id id
    Function.bijective_id).trans ?_
  rw [Matrix.submatrix_id_id]

/-- **The deep factor is independent of the leading tail layer `A' 0`.** Overwriting `A' 0` does not
change `sjDeepFactor`, because the front-peel remainder reads only the tail-of-tail
`Atail (tailChain M) A'` (the layers `A' 1, …, A' L`, indexed through `Fin.succ`). The load-bearing
fact for the `A' 0`-vs-deeper Pi-split. -/
theorem sjDeepFactor_update_zero (M : Fin (L + 1 + 1 + 1) → ℕ) (A' : Params (tailChain M))
    (B : Matrix (Fin ((tailChain M) ((0 : Fin (L + 1)).castSucc)))
      (Fin ((tailChain M) ((0 : Fin (L + 1)).succ))) ℝ) :
    sjDeepFactor M (Function.update A' 0 B) = sjDeepFactor M A' := by
  have hAtail : Atail (tailChain M) (Function.update A' 0 B) = Atail (tailChain M) A' := by
    funext s
    unfold Atail
    rw [Function.update_of_ne (Fin.succ_ne_zero s)]
  unfold sjDeepFactor
  rw [hAtail]

/-- **The measure-side entry with the explicit deep factor (Classical.choose-free).** As
`gammaPeelIntegral_sjGoodMap_eq`, but the deep factor is the explicit `sjDeepFactor M A'`, whose
`A' 0`-independence (`sjDeepFactor_update_zero`) the Pi-split consumes. Same proof: the banked
measure-side entry + the pointwise integrand rewrite (`sjTail_factor_explicit` + gap A). -/
theorem gammaPeelIntegral_sjGoodMap_eq' (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      = ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
            ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
                Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
              ENNReal.ofReal
                ((sjGoodChartLoss x Γ ((A' 0).submatrix (blockSplitEquiv κ) id)
                    (sjDeepFactor M A')) ^ (-c')) := by
  rw [gammaPeelIntegral_schurShearFree_eq M t ρ κ c']
  refine lintegral_congr (fun A' => lintegral_congr (fun x => lintegral_congr (fun Γ => ?_)))
  have heq : freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)
      = sjGoodChartLoss x Γ ((A' 0).submatrix (blockSplitEquiv κ) id) (sjDeepFactor M A') := by
    rw [sjTail_factor_explicit M t κ A']
    exact freedSchurLoss_eq_sjGoodChartLoss x Γ ((A' 0).submatrix (blockSplitEquiv κ) id)
      (sjDeepFactor M A')
  rw [heq]

end DLNFibre.DLN.RLCT
