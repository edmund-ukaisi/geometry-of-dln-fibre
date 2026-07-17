import DLNFibre.DLN.RLCT.Engine.ResolutionTree
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineObligations` — the engine's obligations (edge-labelled, ChartBridge)

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules apply.**
The transform-only Aoyagi engine's obligations over the council-adopted EDGE-LABELLED carrier
(`Engine.ResolutionTree`), with the CoV `ChartBridge` replacing the refuted abstract `ChartsCover`
(lane-2 vacuity: an all-`univ` atlas satisfied the old shape while the box diverged). **Statement
detail is deliberately loose where marked; the fork-level SHAPE is the forecast** — in particular
`LeafJacobian` is held deliberately loose pending the Q5 supplemental ruling (fderiv-over-flat vs
RLCT-transport).

Bundle shape (council of two): `CanonicalResolution = IsFullMonomialization ∧ StepRel-everywhere ∧
branch-rooted ∧ ChartBridge ∧ (exponent hooks + tStar emitted-path attainment)`. `StepRel` is
edge-relational (case-keyed: case11 parent-referencing merge / case12 new pivot + J advance / case2
shared-δ over all generators). `ChartBridge` = UPSTAIRS image cover + per-leaf InjOn + `LeafPullback`
+ `LeafJacobian`, with `chartMap` derived-not-independent (the vacuity closes at type strength). The
single construction hole is `monomialization_terminates`; the single analytic hole is `region_glue`
(the P8 CoV lemma). **Layer-B fence: only `region_glue` integrates.**
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Parent–edge read-off (for the edge-relational `StepRel`) -/

mutual
/-- Parent-step / edge pairs of the tree — the domain of the edge-relational `StepRel`. -/
def stepEdges {M : Fin (L + 1) → ℕ} : ResolutionTree M → List (StepData M × Edge M)
  | .leaf _ => []
  | .branch n edges => edges.map (fun e => (n, e)) ++ edgesStepEdges edges
/-- Parent–edge pairs reachable through a list of edges. -/
def edgesStepEdges {M : Fin (L + 1) → ℕ} : List (Edge M) → List (StepData M × Edge M)
  | [] => []
  | .mk _ _ c :: es => stepEdges c ++ edgesStepEdges es
end

/-! ## Supporting forecast predicates (loose detail; shape-locked) -/

/-- **The residual base form** for a leaf: `‖z‖²` on the `resRank` disjoint Morse coordinates
`resCoord` for a Morse core (`resRank > 0`, vanishing at the origin), or the constant `1` for a
bounded unit (`resRank = 0`). A single squeeze `lo·baseForm ≤ residualCore ≤ hi·baseForm` then covers
both cases (Codex §8 #1/#4). -/
def residualBaseForm (l : LeafData (L := L) M) (u : Fin l.numChartVar → ℝ) : ℝ :=
  if l.resRank = 0 then 1 else ∑ i : Fin l.resRank, (u (l.resCoord i)) ^ 2

/-- **The loss-pullback identity** (cert-bridge-design (P); Codex §8 #1/#4). On the chart source box,
`F ∘ chartMap = (∏ u²) · residualCore` — the divisor monomial `∏ (u_{divCoord k})²` times a
`residualCore` squeezed between positive multiples of the residual base form (`‖z‖²` Morse core, or
the constant `1` for a bounded unit). No fderiv (route-neutral). -/
def LeafPullback (l : LeafData (L := L) M) : Prop :=
  ∃ (residualCore : (Fin l.numChartVar → ℝ) → ℝ) (lo hi : ℝ), 0 < lo ∧
    ∀ u ∈ l.srcBox,
      frobSq (prod M (l.chartMap u))
          = (∏ k : Fin l.numDiv, (u (l.divCoord k)) ^ 2) * residualCore u ∧
      lo * residualBaseForm l u ≤ residualCore u ∧ residualCore u ≤ hi * residualBaseForm l u

/-- **The Jacobian ledger** (cert-bridge-design (J)) — DELIBERATELY LOOSE pending the Q5 ruling
(fderiv-over-flat-coords vs the RLCT-transport route; `Params M` is not a normed space, so a direct
`HasFDerivWithinAt … → Params M` is ill-typed). Route-neutral placeholder: the chart's monomial
Jacobian ledger is positive-bounded on the source box. The exact identity `|det Dφ| = ∏ u^{divExp−1} ·
unit` is pinned once Q5 lands. -/
def LeafJacobian (l : LeafData (L := L) M) : Prop :=
  ∃ Jhi : ℝ, 0 < Jhi ∧ l.srcBox.Nonempty

/-- **The CoV bridge** (cert-bridge-design (d)): the chart atlas covers an UPSTAIRS-open neighbourhood
of the zero locus via chart IMAGES (downstairs images are not open), and every leaf chart is injective
with a valid pullback + Jacobian ledger. Replaces the refuted abstract `ChartsCover`. -/
def ChartBridge (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  (∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartMap '' l.srcBox) ∧
    (∀ l ∈ ResolutionTree.leaves t,
      Set.InjOn l.chartMap l.srcBox ∧ LeafPullback l ∧ LeafJacobian l)

/-- **The edge-relational per-step invariant** (council: case-keyed identities). For a parent step `n`
and one of its edges `e`:
* **case 2** — a divisor of exponent `(M(S)−J)(M(S+1)−J) = resRows·resCols` that divides EVERY residual
  generator (the shared-δ coupling; via `n.support`).
* **case 1(1)** — the exponent-merge into an existing divisor at clearing level `J` (`n.cleared`).
* **case 1(2)** — a NEW pivot divisor at level `J` entering the monomial vector (advances `J`).
(Shape-locked; the ideal-preservation content + the child J-advance coupling are the tide's.) -/
def StepRel {M : Fin (L + 1) → ℕ} (n : StepData M) (e : Edge M) : Prop :=
  (e.case = StepCase.case2 → ∃ k : Fin n.numDiv,
      n.divExp k = n.resRows * n.resCols ∧ ∀ g : Fin n.numGen, k ∈ n.support g) ∧
  (e.case = StepCase.case11 → ∃ k : Fin n.numDiv, n.divTilde k = n.cleared) ∧
  (e.case = StepCase.case12 → ∃ k : Fin n.numDiv,
      n.divTilde k = n.cleared ∧ ∃ i : Fin n.numB, 0 < n.bExp i k)

/-- **Full monomialisation**: each leaf's terminal divisor exponent equals `Mval` of its rank profile
(Aoyagi p.22). The leaf chain is enforced at type strength by `LeafData.bChain`. -/
def IsFullMonomialization {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : Prop :=
  ∀ l ∈ ResolutionTree.leaves t, ∀ k : Fin l.numDiv,
    l.divExp k = (Mval M (l.divProfile k)).toNat

/-- **A canonical resolution** — the bundle every downstream obligation projects from (council-adopted
edge-labelled shape). Conjoins: full monomialisation; the edge-relational `StepRel` on every
parent–edge pair; the branch-rooted base `S = J = 0`; the CoV `ChartBridge`; and the exponent hooks —
`minAdm M` is a terminal exponent (attained by an emitted leaf's profile) and lower-bounds them all
(the tStar realized-path attainment: the minimiser is on the atlas, not merely QIP-admissible). -/
def CanonicalResolution (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  IsFullMonomialization t ∧
    (∀ p ∈ stepEdges t, StepRel p.1 p.2) ∧
      (∃ (n : StepData M) (edges : List (Edge M)),
          t = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0) ∧
        ChartBridge M t ∧
          ((∀ e ∈ ResolutionTree.terminalExponents t, minAdm M ≤ e) ∧
            minAdm M ∈ ResolutionTree.terminalExponents t)

/-! ## The construction hole + the canonical resolution -/

/-- **Monomialisation terminates into a canonical resolution** (map: `monomialization-termination`;
the ONE construction hole). Layer B; structural. The coverage/step/exponent/CoV CONTENT lives here;
the obligations below are its projections. -/
@[blueprint] theorem monomialization_terminates (M : Fin (L + 1) → ℕ) :
    ∃ t : ResolutionTree M, CanonicalResolution M t := by
  sorry

/-- **The canonical resolution** of `M`. A blueprint forecast (rests on the sorried construction). -/
@[blueprint] noncomputable def resolutionOf (M : Fin (L + 1) → ℕ) : ResolutionTree M :=
  (monomialization_terminates M).choose

/-- The canonical resolution satisfies the full bundle. -/
@[blueprint] theorem resolutionOf_spec (M : Fin (L + 1) → ℕ) :
    CanonicalResolution M (resolutionOf M) :=
  (monomialization_terminates M).choose_spec

/-- The canonical resolution is a full monomialisation — the precondition of `region_glue`. -/
@[blueprint] theorem resolutionOf_isFullMonomialization (M : Fin (L + 1) → ℕ) :
    IsFullMonomialization (resolutionOf M) :=
  (resolutionOf_spec M).1

/-! ## The obligations (projections of the bundle) + the analytic hole -/

/-- **Case-step invariant** (map: `case-step-lemmas`). Every parent–edge pair of the canonical
resolution satisfies its case-keyed `StepRel`. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem case_step_invariant (M : Fin (L + 1) → ℕ) :
    ∀ p ∈ stepEdges (resolutionOf M), StepRel p.1 p.2 :=
  (resolutionOf_spec M).2.1

/-- **Reduction layer** (map: `reduction-layer`). The regular peel: the canonical resolution begins at
the base of the invariant `S = J = 0`. STRUCTURAL (Layer-B fence). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem reduction_layer (M : Fin (L + 1) → ℕ) :
    ∃ (n : StepData M) (edges : List (Edge M)),
      resolutionOf M = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0 :=
  (resolutionOf_spec M).2.2.1

/-- **Coverage — THE HARD PART** (map: `coverage-theorem`, owned by coverage-design). The canonical
resolution's chart atlas covers an UPSTAIRS-open box-neighbourhood of the zero locus via chart images,
with per-leaf injectivity + pullback + Jacobian. WITHOUT `rlct = c*`. A projection of
`resolutionOf_spec`. -/
@[blueprint] theorem coverage_theorem (M : Fin (L + 1) → ℕ) :
    ChartBridge M (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.1

/-- **Exponent-ledger bridge** (map: `exponent-ledger-bridge`). `minAdm M` is the minimum of the
resolution's terminal divisor exponents (attained by an emitted leaf). Consumes `minAdm`/`Mval`
verbatim. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem exponent_ledger_bridge (M : Fin (L + 1) → ℕ) :
    (∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), minAdm M ≤ e) ∧
      minAdm M ∈ ResolutionTree.terminalExponents (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.2

/-- **Region glue** (map: `region-glue`; the ONE analytic hole). ASSEMBLY ONLY: given the CoV bridge,
the box integral is finite whenever `c'` is below half every terminal divisor exponent — the banked
Layer-D monomial/radial reads, glued over the upstairs-open finite subcover. Precondition
`IsFullMonomialization` (chain leaves ⟹ separated read exact, cert-d3 A1). The elementary-blow-up
box-CoV / the RLCT-transport scaling bridge is the P8 lemma. -/
@[blueprint] theorem region_glue (M : Fin (L + 1) → ℕ)
    (hbridge : ChartBridge M (resolutionOf M)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT.Engine
