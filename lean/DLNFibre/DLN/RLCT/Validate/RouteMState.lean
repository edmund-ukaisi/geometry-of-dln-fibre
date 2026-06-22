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

/-! ## Per-node `(d,k,h)` accumulation — appending a pivot divisor (fork-independent value bedrock)

A C1/C5 blow-up node ADDS one exceptional divisor to the accumulated chart datum: a fresh axis with
`(k, h) = (1, card−1)` (the codim-`card` pivot stratum, `axisRatio = card/2`). On `MonoData` this is
`appendDivisor` (snoc the new axis at the end). Its effect on the chart threshold is the `⨅`/`min`
update `monomialThreshold (append) = min (card/2) (monomialThreshold old)` — the binding `⨅` takes
the min with the new axis's ratio. Pure threshold combinatorics (via `monomial_rlct.1`), INDEPENDENT
of how the recursion accumulates: the leaf-data semantics every division (A/B/C) shares. -/

/-- `⨅` over `Fin (d+1)` splits as `min` of the last coordinate and the `⨅` over the `castSucc`
prefix. Generic `ℝ≥0∞` fact (`le_antisymm` + `Fin.lastCases`, no named Mathlib `Fin`-iInf lemma). -/
theorem iInf_fin_succ_eq_min_last {d : ℕ} (f : Fin (d + 1) → ℝ≥0∞) :
    (⨅ j : Fin (d + 1), f j) = min (f (Fin.last d)) (⨅ j : Fin d, f j.castSucc) := by
  apply le_antisymm
  · exact le_min (iInf_le _ (Fin.last d)) (le_iInf fun j => iInf_le _ j.castSucc)
  · refine le_iInf fun j => ?_
    refine Fin.lastCases ?_ ?_ j
    · exact min_le_left _ _
    · exact fun i => le_trans (min_le_right _ _) (iInf_le _ i)

/-- Append a pivot divisor `(k,h) = (1, c−1)` (the codim-`c` exceptional axis) to a `MonoData`. -/
def MonoData.appendDivisor (md : MonoData) (c : ℕ) : MonoData :=
  ⟨md.d + 1, Fin.snoc md.k 1, Fin.snoc md.h (c - 1)⟩

/-- **Per-node threshold update (the value-side accumulation step).** Appending a codim-`c` pivot
divisor `(1, c−1)` takes the chart threshold to the `min` of its old value and the new axis's ratio
`c/2`: `monomialThreshold (md.appendDivisor c) = min (c/2) (monomialThreshold md)` (`1 ≤ c`). The
`⨅ axisRatio` over the snoc'd family splits (via `iInf_fin_succ_eq_min_last`) into the last axis
(`axisRatio (c−1) 1 = c/2`, `axisRatio_regularSeq`) and the prefix (the old `⨅`). The `min`-fold is
how the binding minimal-codim divisor controls the cover `⨅` (`achiever` / `threshold_ge`). Rests on
`monomial_rlct` (S2). -/
theorem monomialThreshold_appendDivisor (md : MonoData) (c : ℕ) (hc : 1 ≤ c) :
    monomialThreshold (md.appendDivisor c).d (md.appendDivisor c).k (md.appendDivisor c).h
      = min ((c : ℝ≥0∞) / 2) (monomialThreshold md.d md.k md.h) := by
  rw [(monomial_rlct (md.appendDivisor c).d (md.appendDivisor c).k (md.appendDivisor c).h).1,
    (monomial_rlct md.d md.k md.h).1]
  simp only [MonoData.appendDivisor]
  rw [iInf_fin_succ_eq_min_last]
  congr 1
  · rw [Fin.snoc_last, Fin.snoc_last, axisRatio_regularSeq c hc]
  · exact iInf_congr fun j => by rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

end DLNFibre.DLN.RLCT
