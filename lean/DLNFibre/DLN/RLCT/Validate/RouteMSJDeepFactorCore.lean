import DLNFibre.DLN.RLCT.Validate.RouteMSJTailSplit

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDeepFactorCore` — the deep factor after the Pi-split

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain, transport step (a) bridge.** After the
`A' 0`-vs-deeper Pi-split (`eFrontTail`, `RouteMSJTailSplit`), the tail parameter is reassembled as
`eFrontTail.symm (A' 0, deeper)`. The deep factor `sjDeepFactor` of this reassembly depends ONLY on
the deeper layers, NOT on the leading layer `A' 0` — what the Pi-split needs to pull `sjDeepFactor`
out of the `A' 0`-box (the pivot-row→`v` translation) as a constant. This module bundles that as
`sjDeepFactorCore` (Codex `codex/transport-answer.md` §2).

* **`sjDeepFactorCore M rest`** — the deep factor as a function of the deeper layers only.
* **`sjDeepFactor_eFrontTail_symm`** — the bridge: `sjDeepFactor M (eFrontTail.symm (U, rest)) =
  sjDeepFactorCore M rest` for ANY leading layer `U`. The deeper layers of the reassembly are
  exactly `rest` (from `eFrontTail.apply_symm_apply` via `Prod.snd`), and `sjDeepFactor` reads only
  (`Atail` reads the `.succ` layers).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators

variable {L : ℕ}

/-- **The deep factor as a function of the deeper layers only.** `sjDeepFactorCore M rest =
sjDeepFactor M (eFrontTail.symm (0, rest))` — the deep factor of the tail reassembled with a zero
leading layer; by `sjDeepFactor_eFrontTail_symm` this value is independent of the leading layer. -/
noncomputable def sjDeepFactorCore (M : Fin (L + 1 + 1 + 1) → ℕ)
    (rest : ∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
        → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) :
    Matrix (Fin ((tailChain M) ((0 : Fin (L + 1)).succ)))
      (Fin ((tailChain M) (Fin.last (L + 1)))) ℝ :=
  sjDeepFactor M ((eFrontTail M).symm (0, rest))

/-- **The deep factor of the Pi-split reassembly is `A' 0`-independent.** For ANY leading layer `U`,
`sjDeepFactor M (eFrontTail.symm (U, rest)) = sjDeepFactorCore M rest`. The deeper layers of
`eFrontTail.symm (U, rest)` are exactly `rest` (forward `apply_symm_apply` + `Prod.snd`), so the two
reassemblies (leading layer `U` vs `0`) share their `Atail` — which is all `sjDeepFactor` reads. -/
theorem sjDeepFactor_eFrontTail_symm (M : Fin (L + 1 + 1 + 1) → ℕ)
    (U : Fin ((tailChain M) ((0 : Fin (L + 1)).castSucc))
        → Fin ((tailChain M) ((0 : Fin (L + 1)).succ)) → ℝ)
    (rest : ∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
        → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) :
    sjDeepFactor M ((eFrontTail M).symm (U, rest)) = sjDeepFactorCore M rest := by
  have hsucc : ∀ (W : Fin ((tailChain M) ((0 : Fin (L + 1)).castSucc))
        → Fin ((tailChain M) ((0 : Fin (L + 1)).succ)) → ℝ) (s : Fin L),
      ((eFrontTail M).symm (W, rest)) s.succ = rest s := by
    intro W s
    exact congrFun (congrArg Prod.snd ((eFrontTail M).apply_symm_apply (W, rest))) s
  have hAtail : Atail (tailChain M) ((eFrontTail M).symm (U, rest))
      = Atail (tailChain M) ((eFrontTail M).symm (0, rest)) := by
    funext s
    unfold Atail
    rw [hsucc U s, hsucc 0 s]
  unfold sjDeepFactorCore sjDeepFactor
  rw [hAtail]

end DLNFibre.DLN.RLCT
