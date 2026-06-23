import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.SchurState

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMClassify` — the `routeStep` leaf classifier (fm3, sub-1)

The terminal-node test for the general `routeStep` dispatcher (`RouteMRecursion.routeStep`), built as a
standalone, decidable building block. A node `M` is a **leaf** exactly when its minimal admissible codim
`minAdm M = ((Adm M).inf' Mval).toNat` is `0`: no positive-codim pivot stratum remains, so the residual
core is a unit and the chain has bottomed out. This is the dispatcher's piece (1) — the residual rank-defect
classifier — stated honestly: it is NOT "no `schurState` applies" (the `(2,2,0)`-style nodes still admit a
`schurState` split yet have `minAdm = 0`, so they ARE leaves), and it is non-vacuous (`(2,2,2)` has
`minAdm = 3 > 0`, so it is NOT a leaf — avoiding the docstring's trap (i), leaf-everywhere).

The leaf datum is `leafMonoData 0` (the empty `d = 0` base, threshold `⊤`): a unit leaf carries no monomial,
so it never binds the cover `⨅`; the value comes from the pivot divisors appended ABOVE it on the path
(`MonoData.appendDivisor`). `leafThreshold_eq_top` records this. This file does NOT touch the `routeStep`
`sorry` — it banks the leaf arm for sub-3's assembly.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The leaf test**: `M` is a leaf iff its minimal admissible codim is `0` (no positive-codim pivot
stratum remains — the residual core is a unit). The honest terminal classifier (dispatcher piece (1)):
when `minAdm M = 0`, every admissible `T` gives `Mval M T = 0`, so there is no genuine blow-up to perform
and the recursion stops. Decidable (`Adm`/`Mval` concrete). -/
def isLeafNode (M : Fin (L + 1) → ℕ) : Prop :=
  ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat = 0

instance (M : Fin (L + 1) → ℕ) : Decidable (isLeafNode M) := by
  unfold isLeafNode; infer_instance

/-- **The leaf arm of the dispatcher.** At a leaf node the chart carries the empty `d = 0` monomial datum
`leafMonoData 0` (threshold `⊤`): no monomial of its own, the value rides the divisors appended above. The
`RouteStep.leaf` constructor, root-anchored trivially (a leaf carries no codim/witness — those live on the
branch cells above). -/
def leafStep (M₀ M : Fin (L + 1) → ℕ) : RouteStep M₀ M :=
  .leaf (leafMonoData 0)

/-- **The leaf datum's threshold is `⊤`.** The leaf imposes no monomial threshold, so it never binds the
cover `⨅` — the per-leaf value comes entirely from the pivot divisors accumulated above it. (Restates
`leafMonoData_threshold` at the leaf-arm datum, the contract sub-3 relies on.) -/
theorem leafStep_threshold :
    monomialThreshold (leafMonoData 0).d (leafMonoData 0).k (leafMonoData 0).h = ⊤ :=
  leafMonoData_threshold 0

/-! ## Non-vacuity anchors — the classifier separates genuine branches from terminal leaves -/

/-- `(2,2,2)` is NOT a leaf (`minAdm = 3 > 0`): the dispatcher must branch on it. Guards against the
docstring's trap (i) — leaf-everywhere would make the atlas trivial (threshold `⊤ ≠ ½·minAdm`). -/
theorem not_isLeafNode_M222 : ¬ isLeafNode (fun _ => 2 : Fin 3 → ℕ) := by decide

/-- A bottomed-out node `(0,0,2)` IS a leaf (`minAdm = 0`): both pivot vertices have collapsed, no stratum
left. The terminal case the recursion descends to. -/
theorem isLeafNode_collapsed : isLeafNode (![0, 0, 2] : Fin 3 → ℕ) := by decide

/-- `(2,2,0)` IS a leaf (`minAdm = 0`) **even though** `schurState` would still apply (both pivot vertices
are `≥ 1`): the leaf test is `minAdm = 0`, NOT "no `schurState` applies". This is the load-bearing fidelity
point — a `schurState`-driven recursion that stopped only when the split fails would over-pivot here. -/
theorem isLeafNode_degenerate_tail : isLeafNode (![2, 2, 0] : Fin 3 → ℕ) := by decide

end DLNFibre.DLN.RLCT
