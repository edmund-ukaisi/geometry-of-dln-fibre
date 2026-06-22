import DLNFibre.DLN.RLCT.Skeleton
import Mathlib.Data.Prod.Lex

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMState` — the Route M recursion carrier + measure + leaf datum (fm3)

The complete FOUNDATION for the Route M dispatcher (`RouteMTree.lean`): the node state `RouteState`,
the well-founded termination measure `lex(L, ΣM, ncDefect)`, the per-leaf monomial datum `MonoData`,
and the leaf (unit) datum + its `monomialThreshold = ⊤` fact. Split out from the dispatcher so this
committable bedrock banks independently of the (in-progress) `classify`/cover-fact bodies. Fully
proven (no proof gaps); rests on `monomial_rlct` (the S2 cited threshold axiom) only.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-- A node state: the chain depth `L` and the widths `M`. The recursion's carrier. -/
structure RouteState where
  L : ℕ
  M : Fin (L + 1) → ℕ

/-- `ΣM`, the total width (the second lex component; drops at a C1 node). -/
def RouteState.widthSum (S : RouteState) : ℕ := ∑ i, S.M i

/-- The normal-crossing defect (the third lex component; drops at a C3 NC-completion pass). The number
of non-normal-crossing exceptional intersections; pinned at `0` here (refined per-leaf by C3). -/
def RouteState.ncDefect (_S : RouteState) : ℕ := 0

/-- The termination measure: `lex(L, ΣM, ncDefect)` on `ℕ³` (well-founded). -/
abbrev RouteMeasure := ℕ ×ₗ ℕ ×ₗ ℕ

/-- The lex measure of a state. -/
def routeMeasure (S : RouteState) : RouteMeasure :=
  toLex (S.L, toLex (S.widthSum, S.ncDefect))

/-- The recursion's well-founded relation: strictly-smaller lex measure. -/
def routeRel (S T : RouteState) : Prop := routeMeasure S < routeMeasure T

/-- `routeRel` is well-founded (pullback of `<` on `ℕ³ₗ` along `routeMeasure`). -/
theorem routeRel_wf : WellFounded routeRel :=
  InvImage.wf routeMeasure wellFounded_lt

/-- The per-leaf monomial datum: dimension `d` + the `(k, h)` exponents for `monomialThreshold`. -/
structure MonoData where
  d : ℕ
  k : Fin d → ℕ
  h : Fin d → ℕ

/-- **The leaf (unit) datum.** At a leaf (`L=1` / rank-0 core, `F = ‖C₁‖²` already a unit after all
singular directions are blown up), the chart carries NO monomial: `k = h = 0` over the `d` ambient
coordinates (the (d,k,h)-accumulation BASE; each blow-up node SETS its pivot axis to `(1, card−1)`
outward). NOT a smooth block `d/2` — that is the off-path additive squeeze; the `d/2`-type RLCT rides
the accumulated pivot `(k,h)` via `⨅ axisRatio`. -/
def leafMonoData (d : ℕ) : MonoData := ⟨d, fun _ => 0, fun _ => 0⟩

/-- **The leaf threshold is `⊤`.** A unit leaf (`k ≡ 0`) imposes no monomial threshold:
`monomialThreshold d 0 h = ⨅ⱼ axisRatio (h j) 0 = ⨅ⱼ ⊤ = ⊤` (every axis is a spectator, `axisRatio _ 0
= ⊤`). So the leaf NEVER binds the cover `⨅` — the RLCT comes entirely from the accumulated pivot
divisors above it. (Rests on `monomial_rlct`, the S2 cited threshold axiom.) -/
theorem leafMonoData_threshold (d : ℕ) :
    monomialThreshold (leafMonoData d).d (leafMonoData d).k (leafMonoData d).h = ⊤ := by
  rw [(monomial_rlct (leafMonoData d).d (leafMonoData d).k (leafMonoData d).h).1]
  simp only [leafMonoData]
  exact le_antisymm le_top (le_iInf (fun j => by rw [axisRatio]; simp))

end DLNFibre.DLN.RLCT
