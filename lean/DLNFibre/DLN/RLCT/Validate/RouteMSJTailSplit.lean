import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepFactor

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJTailSplit` — the `A' 0`-vs-deeper Pi-split (transport step a)

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain, transport step (a).** The measure transport
(route A, `codex/transport-answer.md`) begins by isolating the leading tail layer `A' 0` from the
deeper layers `A' 1, …, A' L`, so the `A' 0`-box carries the pivot-row→`v` translation
(`sjGoodChartLoss_pivotRows_translate_eq`, `RouteMSJPivotTranslate`) while the deeper layers — which
determine `sjDeepFactor` (`sjDeepFactor_update_zero`, `RouteMSJDeepFactor`) — stay fixed. This
module banks that Pi-split, mirroring the banked `eFront` (`RouteMSJResolution`) but applied to
`Params (tailChain M)`.

* **`eFrontTail`** — the measurable equivalence `Params (tailChain M) ≃ᵐ (A' 0 layer) × (deeper
  layers)` (`MeasurableEquiv.piFinSuccAbove … 0`), MP (`measurePreserving_eFrontTail`).
* **`eFrontTail_preimage_box`** — the box factorization: the tail parameter box pulls back to the
  product of the leading-layer box and the deeper-layers box (`Fin.cases` on the layer index).
* **`tailParams_pi_split`** — the split integral identity: `∫_{A' ∈ paramsBoxM} f A'`
  `= ∫_{(A' 0, deeper) ∈ box ×ˢ box} f (eFrontTail.symm …)`. Transport through the MP `eFrontTail`
  (`setLIntegral_comp_preimage_emb`) + the box factorization.

The composition consuming this: split the leading-layer integral further into pivot-rows ×
corank-rows (`sumPiEquivProdPi`/`splitCols` template), apply the pivot-row translation
(`RouteMSJPivotTranslate`), holding `sjDeepFactor` fixed (`sjDeepFactor_update_zero`), then feed the
good-chart endpoint.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (MP Pi-reindex + box preimage).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The leading-tail-layer Pi-split** `Params (tailChain M) ≃ᵐ (A' 0 layer) × (deeper layers)`
(`piFinSuccAbove` at index `0`). The `eFront` analogue for the tail chain: the first factor is the
leading tail layer `A' 0` (size `M₁ × M₂`), the second the deeper layers `A' 1, …, A' L`. -/
noncomputable def eFrontTail (M : Fin (L + 1 + 1 + 1) → ℕ) :
    Params (tailChain M) ≃ᵐ
      (Fin ((tailChain M) ((0 : Fin (L + 1)).castSucc))
          → Fin ((tailChain M) ((0 : Fin (L + 1)).succ)) → ℝ)
        × (∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
            → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) :=
  MeasurableEquiv.piFinSuccAbove
    (fun s : Fin (L + 1) => Fin ((tailChain M) s.castSucc) → Fin ((tailChain M) s.succ) → ℝ) 0

/-- `eFrontTail` is measure-preserving (`volume_preserving_piFinSuccAbove`). -/
theorem measurePreserving_eFrontTail (M : Fin (L + 1 + 1 + 1) → ℕ) :
    MeasurePreserving (eFrontTail M) (volume : Measure (Params (tailChain M))) volume :=
  volume_preserving_piFinSuccAbove
    (fun s : Fin (L + 1) => Fin ((tailChain M) s.castSucc) → Fin ((tailChain M) s.succ) → ℝ) 0

/-- `eFrontTail M A' = (A' 0, fun s => A' (0.succAbove s))` — leading layer and deeper layers. -/
theorem eFrontTail_apply (M : Fin (L + 1 + 1 + 1) → ℕ) (A' : Params (tailChain M)) :
    eFrontTail M A' = (A' 0, fun s => A' ((0 : Fin (L + 1)).succAbove s)) := rfl

/-- **The box factorization.** The tail parameter box pulls back along `eFrontTail` to the product
of the leading-layer box and the deeper-layers box (`Fin.cases` on the layer index, as
`eFront_preimage_box`). -/
theorem eFrontTail_preimage_box (M : Fin (L + 1 + 1 + 1) → ℕ) :
    eFrontTail M ⁻¹'
        ((matBox ((tailChain M) ((0 : Fin (L + 1)).castSucc))
            ((tailChain M) ((0 : Fin (L + 1)).succ)) 1)
          ×ˢ {g : (∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
              → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) |
              ∀ s i j, g s i j ∈ Set.Icc (-1 : ℝ) 1})
      = paramsBoxM (tailChain M) 1 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBoxM, Set.mem_setOf_eq, eFrontTail_apply]
  constructor
  · rintro ⟨h0, htail⟩ s
    refine Fin.cases (fun i j => ?_) (fun s' i j => ?_) s
    · exact h0 i j
    · exact htail s' i j
  · intro h
    exact ⟨fun i j => h 0 i j, fun s' i j => h ((0 : Fin (L + 1)).succAbove s') i j⟩

/-- **The `A' 0`-vs-deeper Pi-split integral identity.** For any `ℝ≥0∞`-valued `f` on the tail
parameter, the tail-box integral equals the product integral over the leading-layer box and the
deeper-layers box, with `A'` reassembled by `eFrontTail.symm`. Transport through the MP `eFrontTail`
(`setLIntegral_comp_preimage_emb`) + the box factorization (`eFrontTail_preimage_box`). The step-(a)
foundation the transport builds the leading-layer row-split + pivot translation on. -/
theorem tailParams_pi_split (M : Fin (L + 1 + 1 + 1) → ℕ) (f : Params (tailChain M) → ℝ≥0∞) :
    ∫⁻ A' in paramsBoxM (tailChain M) 1, f A'
      = ∫⁻ p in (matBox ((tailChain M) ((0 : Fin (L + 1)).castSucc))
            ((tailChain M) ((0 : Fin (L + 1)).succ)) 1)
          ×ˢ {g : (∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
              → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) |
              ∀ s i j, g s i j ∈ Set.Icc (-1 : ℝ) 1},
          f ((eFrontTail M).symm p) := by
  have h := (measurePreserving_eFrontTail M).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (eFrontTail M))
    (fun p => f ((eFrontTail M).symm p))
    ((matBox ((tailChain M) ((0 : Fin (L + 1)).castSucc))
        ((tailChain M) ((0 : Fin (L + 1)).succ)) 1)
      ×ˢ {g : (∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
          → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) |
          ∀ s i j, g s i j ∈ Set.Icc (-1 : ℝ) 1})
  rw [eFrontTail_preimage_box] at h
  simp only [MeasurableEquiv.symm_apply_apply] at h
  exact h

end DLNFibre.DLN.RLCT
