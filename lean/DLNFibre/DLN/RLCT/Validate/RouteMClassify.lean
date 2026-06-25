import DLNFibre.DLN.RLCT.Validate.RouteMLeaf
import DLNFibre.DLN.RLCT.Validate.RouteMRecursion

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMClassify` — the `RouteStep`-valued leaf ARM (fm3, sub-1)

The leaf CLASSIFIER (`isLeafNode`, its exact characterization `isLeafNode_iff_width_zero`, and the branch
precondition `schurState_hlo_of_not_isLeafNode`) lives UPSTREAM in `RouteMLeaf` (so `RouteMRecursion.routeStep`
can consume it). This file is the thin downstream layer carrying the `RouteStep`-valued leaf ARM — `leafStep`
(the `.leaf (leafMonoData 0)` constructor) + its threshold fact — which needs the `RouteStep` type from
`RouteMRecursion`. (Re-exports `RouteMLeaf` so existing consumers of `RouteMClassify` are unaffected.)
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The leaf arm of the dispatcher.** At a leaf node the chart carries the empty `d = 0` monomial datum
`leafMonoData 0` (threshold `⊤`): no monomial of its own, the value rides the divisors appended above. The
`RouteStep.leaf` constructor (a leaf carries no codim/witness — those live on the branch cells above). The
`⊤` is the non-binding path-terminator (pinned in `RouteMState.foldFamily_iInf_eq_half_minAdm`). -/
def leafStep (M₀ M : Fin (L + 1) → ℕ) : RouteStep M₀ M :=
  .leaf (leafMonoData 0)

/-- **The leaf datum's threshold is `⊤`.** The leaf imposes no monomial threshold, so it never binds the
cover `⨅` — the per-leaf value comes entirely from the pivot divisors accumulated above it. (Restates
`leafMonoData_threshold` at the leaf-arm datum, the contract sub-3 relies on.) -/
theorem leafStep_threshold :
    monomialThreshold (leafMonoData 0).d (leafMonoData 0).k (leafMonoData 0).h = ⊤ :=
  leafMonoData_threshold 0

end DLNFibre.DLN.RLCT
