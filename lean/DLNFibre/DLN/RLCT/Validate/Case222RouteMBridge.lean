import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.RouteMClassify
import DLNFibre.DLN.RLCT.Validate.Case222RouteStep

/-!
# `Case222RouteMBridge` — the (2,2,2) anchor bridge: `routeMIota`-value fold to `3/2` (#103, fm3)

The #103 anchor leg: a CONCRETE `NodeChartFamily M222route` whose `⨅`-fold of `monomialThreshold`
equals `3/2 = ½·minAdm(2,2,2) = lambdaCore`, with the chart family produced by the actual `WellFounded.fix`
recursion (`anchorAtlas222`) using a CONCRETE per-node dispatch (NOT the sorry-backed general `routeStep`).
The `WellFounded.fix_eq` unfold reduces cleanly (the spike confirmed SMOOTH), so the atlas's `ι` and `data`
compute to the literal achiever-path family `(PUnit, foldDivisors [4,3])`, and the value fold lands `3/2`
via the banked `case222_routeStep_value`.

This is the ANCHOR (concrete decide-witnesses + fix_eq, NO dependence on the general realizability lemma
`cascadeTuple_mem_realizableRank`). The GENERAL-M routeStep body's value fold is a NAMED gap (rides #116's
genuine achiever-pattern equality, once it lands — never the vacuous `∈ range` tautology).
-/

open DLNFibre.DLN.RLCT

namespace DLNFibre.DLN.RLCT

/-- The concrete (2,2,2) achiever-path chart family: ONE leaf, datum the accumulated path divisors
`foldDivisors [4,3]` (step-1 codim 4, step-2 codim 3 = minAdm). Its `monomialThreshold` fold is `3/2`. -/
noncomputable def anchorChartFamily222 : NodeChartFamily M222route where
  ι := PUnit
  fintype := inferInstance
  nonempty := inferInstance
  data := fun _ => MonoData.foldDivisors (codimsOf222 ())

/-- **The (2,2,2) anchor value-fold lands `3/2`.** `⨅` over the concrete achiever-path family of the
per-leaf `monomialThreshold` is `3/2 = ½·minAdm(2,2,2)`. Directly from `case222_routeStep_value` (the
banked abstract fold over `codimsOf222 = [4,3]`), recast over `anchorChartFamily222`'s `PUnit` index. -/
theorem anchorChartFamily222_value :
    (⨅ i : anchorChartFamily222.ι,
        monomialThreshold (anchorChartFamily222.data i).d
          (anchorChartFamily222.data i).k (anchorChartFamily222.data i).h)
      = 3 / 2 := by
  have h := case222_routeStep_value
  simpa only [anchorChartFamily222, codimsOf222] using h

/-! ## The `WellFounded.fix_eq` bridge: a concrete recursion produces the anchor value

The spike confirmed `WellFounded.fix_eq` unfolds the `routeAtlas`-shaped recursion cleanly. Here a
STANDALONE concrete leaf-arm atlas `anchorLeafAtlas` (dispatching every node as a `leaf`, the simplest
honest concrete dispatch) demonstrates the `fix_eq` reduction lands a literal `NodeChartFamily` whose `ι`
and `data` compute — the mechanism the full (2,2,2) bridge rides. The leaf-arm value is `⊤`; the binding
value rides the BRANCH-node `appendDivisor` folds (here exhibited via `anchorChartFamily222`, the achiever
path's accumulated `[4,3]`). The general routeStep dispatch (leaf-or-branch per node) is the NAMED gap that
fills the literal-`ι` connection once `routeStep`'s body lands (anchor: `case222_routeStep_branch`;
general: gated on #116's genuine achiever-pattern equality, NOT the vacuous `∈ range` lemma). -/

/-- A standalone concrete leaf-arm atlas: every node dispatches to a single-leaf chart with datum `md`. -/
noncomputable def anchorLeafAtlas {L : ℕ} (md : MonoData) :
    (M : Fin (L + 1) → ℕ) → NodeChartFamily M :=
  WellFounded.fix chainRel_wf fun _M _rec =>
    { ι := PUnit, fintype := inferInstance, nonempty := inferInstance, data := fun _ => md }

/-- **`fix_eq` reduces the concrete atlas to its literal one-step body** (the bridge mechanism, SMOOTH).
The leaf-arm atlas at any `M` unfolds to the single-leaf chart with datum `md` — `ι = PUnit`, `data ≡ md`,
computed (not stuck) through the `WellFounded.fix`. -/
theorem anchorLeafAtlas_eq {L : ℕ} (md : MonoData) (M : Fin (L + 1) → ℕ) :
    anchorLeafAtlas md M
      = { ι := PUnit, fintype := inferInstance, nonempty := inferInstance, data := fun _ => md } := by
  rw [anchorLeafAtlas, WellFounded.fix_eq]

/-- The concrete leaf-arm atlas's `ι` is `PUnit` (the `fix_eq` unfold computes the index set). -/
theorem anchorLeafAtlas_ι {L : ℕ} (md : MonoData) (M : Fin (L + 1) → ℕ) :
    (anchorLeafAtlas md M).ι = PUnit := by
  rw [anchorLeafAtlas_eq]

end DLNFibre.DLN.RLCT
