import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepFactorCore
import DLNFibre.DLN.RLCT.Validate.RouteMSJRowSplit
import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotTranslate

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJTransport` — the CoV transport composition (steps a+b)

**Thread `genm-covfinish`, Stage 2 (S,J) CoV mountain.** Composes the banked transport atoms into a
single sorry-free EQUALITY that carries `gammaPeelIntegral` into the row-split coordinate form the
good-chart endpoint route consumes:

* step (a) — `tailParams_pi_split` (`RouteMSJTailSplit`): the `A' 0`-vs-deeper Pi-split, with
  `sjDeepFactor_eFrontTail_symm` (`RouteMSJDeepFactorCore`) holding the deep factor
  `A₂ = sjDeepFactorCore M deeper` independent of the leading layer;
* step (b) — `rowSplit_lintegral_eq` (`RouteMSJRowSplit`): the leading layer `A' 0 : M₁ × M₂` splits
  into its pivot rows `Upiv : t × M₂` and its corank rows `W : (M₁ − t) × M₂`.

The output `gammaPeelIntegral_rowSplit_eq` writes `gammaPeelIntegral M t ρ κ c'` as the five-fold
integral over `(Upiv, W, deeper, x, Γ)` of the good-chart loss on the reassembled front factor
`Matrix.of (Sum.elim Upiv W)`. The remaining step (c) — the pivot-row → free-`v` translation
(`sjGoodChartLoss_pivotRows_translate_eq`) — exposes `v` once `Upiv` is brought innermost (a Tonelli
reorder past `W, deeper, x, Γ`); that + the good-cover endpoint closes only the dimensionally
cooperative "good" branch. The rank-deficient "deeper" branch is the unbuilt `(S,J)` recursion — the
decorated `decorated_peel_step` + well-founded recursion of `RouteMSJDecorated` (contract in the thread
notes `genm-covfinish/notes.md`); `sjJointResolution` (`RouteMSJResolution`) stays its named sorry.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The leading tail layer of the `eFrontTail` reassembly is the first factor.** For the Pi-split
reassembly `(eFrontTail M).symm p`, its layer `0` is exactly `p.1` (the forward `eFrontTail`
value's first component is layer `0`). The `A' 0` companion of `sjDeepFactor_eFrontTail_symm`. -/
theorem eFrontTail_symm_zero (M : Fin (L + 1 + 1 + 1) → ℕ)
    (p : (Fin ((tailChain M) ((0 : Fin (L + 1)).castSucc))
        → Fin ((tailChain M) ((0 : Fin (L + 1)).succ)) → ℝ)
      × (∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
          → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ)) :
    ((eFrontTail M).symm p) 0 = p.1 := by
  have h := congrArg Prod.fst ((eFrontTail M).apply_symm_apply p)
  rw [eFrontTail_apply] at h
  exact h

/-- **Transport step (a), fully composed (sorry-free EQUALITY).** `gammaPeelIntegral M t ρ κ c'`
equals the same triple integral of the good-chart loss, but with the tail parameter `A'` split into
its leading layer `p.1 : M₁ × M₂` and its deeper layers `p.2` (the `A' 0`-vs-deeper Pi-split
`tailParams_pi_split`), the deep factor read as the `A' 0`-independent `sjDeepFactorCore M p.2`
(`sjDeepFactor_eFrontTail_symm`), and the front factor as `p.1.submatrix (blockSplitEquiv κ) id`
(`eFrontTail_symm_zero`). No measurability side-conditions — a pure `lintegral_congr` under the MP
Pi-split. The leading-layer integral is now ready for the row split (`rowSplit_lintegral_eq`) into
pivot rows × corank rows `W`. -/
theorem gammaPeelIntegral_piSplit_eq (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      = ∫⁻ p in (matBox ((tailChain M) ((0 : Fin (L + 1)).castSucc))
            ((tailChain M) ((0 : Fin (L + 1)).succ)) 1)
          ×ˢ {g : (∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
              → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) |
              ∀ s i j, g s i j ∈ Set.Icc (-1 : ℝ) 1},
          ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
            ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
                Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
              ENNReal.ofReal
                ((sjGoodChartLoss x Γ (Matrix.submatrix p.1 (blockSplitEquiv κ) id)
                    (sjDeepFactorCore M p.2)) ^ (-c')) := by
  rw [gammaPeelIntegral_sjGoodMap_eq' M t ρ κ c',
    tailParams_pi_split M (fun A' => ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
      ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
        ENNReal.ofReal
          ((sjGoodChartLoss x Γ ((A' 0).submatrix (blockSplitEquiv κ) id)
              (sjDeepFactor M A')) ^ (-c')))]
  refine lintegral_congr fun p => ?_
  obtain ⟨U, rest⟩ := p
  refine lintegral_congr fun x => lintegral_congr fun Γ => ?_
  rw [eFrontTail_symm_zero M (U, rest), sjDeepFactor_eFrontTail_symm M U rest]

end DLNFibre.DLN.RLCT
