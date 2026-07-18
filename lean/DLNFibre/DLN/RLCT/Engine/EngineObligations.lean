import DLNFibre.DLN.RLCT.Engine.ResolutionTree
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineObligations` — the engine's obligations

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.** The transform-only Aoyagi engine's obligations over the council-adopted EDGE-LABELLED
carrier, repaired per the fresh-round cert (findings 1–7 + rulings). **Statement detail is loose
where marked; the fork-level SHAPE is the forecast.**

Key repairs (cert-carrier-review):
* `StepRel` now READS `e.child` (via the root accessors) and `e.subst.runLen`, and requires the
  case-specific CHILD update — the case-1(1) exponent-merge `M' = M + J₁·(M^{(S+1)}−J)`, the case-2
  CHILD divisor of exponent `resRows·resCols`, the case-1(2) `cleared` advance (finding 1).
* `terminalExponents` folds in every positive `resRank` (ruling 2a), so
  `hrat`/`exponent_ledger_bridge` cover the `resRank/2` residual threshold (`minAdm ≤ resRank`).
* `LeafJacobian` is the FACTORED transport form `chartMap = ψ ∘ β` (ruling 2b): `ψ` a bounded-unit
  local diffeo carrying full inverse data (feeds `rlctAtOn_boundedUnit_localHomeomorph`), `β` the
  explicit monomial blow-up `|det Dβ| = ∏ |u|^{divExp−1}` (finding 7 abs-value; direct integration).
* `ChartBridge`: a.e.-injectivity off a null set (finding 6), injective/disjoint
  `divCoord`/`resCoord` (finding 5), live-`srcBox` attainment (finding 3). `IsFullMonomialization`
  requires `divProfile ∈ Adm M` (finding 4).

**Layer-B fence: only `region_glue` integrates.** The two holes are `monomialization_terminates` +
`region_glue`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Supporting forecast predicates (loose detail; shape-locked) -/

/-- **The residual base form**: `‖z‖²` on the `resRank` disjoint Morse coordinates `resCoord`
(read off `w` via `paramsEquivFlat`), or the constant `1` for a bounded unit (`resRank = 0`). -/
noncomputable def residualBaseForm (l : LeafData (L := L) M) (w : Params M) : ℝ :=
  if l.resRank = 0 then 1 else ∑ i : Fin l.resRank, (paramsEquivFlat M w (l.resCoord i)) ^ 2

/-- **The loss-pullback identity** (cert-bridge-design (P)): on the source box, `F ∘ chartMap =
(∏ u²) · residualCore`, the divisor monomial times a `residualCore` squeezed between positive
multiples of the base form (`‖z‖²` Morse core or unit `1`). (The monomial is squared, so
sign-safe.) -/
def LeafPullback (l : LeafData (L := L) M) : Prop :=
  ∃ (residualCore : Params M → ℝ) (lo hi : ℝ), 0 < lo ∧
    ∀ w ∈ l.srcBox,
      frobSq (prod M (l.chartMap w))
          = (∏ k : Fin l.numDiv, (paramsEquivFlat M w (l.divCoord k)) ^ 2) * residualCore w ∧
      lo * residualBaseForm l w ≤ residualCore w ∧ residualCore w ≤ hi * residualBaseForm l w

/-- **The Jacobian ledger — FACTORED transport form** (ruling 2b, fork 8). `chartMap = ψ ∘ β` on the
source box, where `β` is the explicit monomial blow-up (`|det Dβ| = ∏ |u|^{divExp−1}`, abs-value —
finding 7; handled by direct monomial integration / the scaling bridge) and `ψ` is a bounded-unit
local diffeomorphism carrying FULL inverse data (forward + inverse identities + `C¹` + determinant
bounded away from `0`/`∞`) — exactly the hypotheses `rlctAtOn_boundedUnit_localHomeomorph` consumes.
The transport was never meant to eat the singular factor: `β` is Aoyagi's monomialized-integrand
chart. -/
def LeafJacobian (l : LeafData (L := L) M) : Prop :=
  ∃ (β ψ ψsymm : Params M → Params M)
    (Dβ Dψ : Params M → (Params M →L[ℝ] Params M)) (lo hi : ℝ), 0 < lo ∧
    (∀ w ∈ l.srcBox, l.chartMap w = ψ (β w)) ∧
    (∀ w ∈ l.srcBox, HasFDerivAt β (Dβ w) w ∧
      |(Dβ w).det|
        = ∏ k : Fin l.numDiv, |paramsEquivFlat M w (l.divCoord k)| ^ (l.divExp k - 1)) ∧
    (∀ v ∈ β '' l.srcBox, ψsymm (ψ v) = v ∧ ψ (ψsymm v) = v ∧
      HasFDerivAt ψ (Dψ v) v ∧ lo ≤ |(Dψ v).det| ∧ |(Dψ v).det| ≤ hi)

/-- **The CoV bridge** (fork 8, repaired). The atlas covers an UPSTAIRS-open neighbourhood of the
zero locus via chart IMAGES; every leaf chart has injective/disjoint divisor & Morse coordinates
(finding 5), is A.E.-INJECTIVE off a null set (finding 6 — a blow-up chart is not injective on the
exceptional fibre), and satisfies `LeafPullback` + `LeafJacobian`; and each leaf's `chartMap` is the
DERIVED fold of its root→leaf edge substitutions (coherence). -/
def ChartBridge (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  (∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartMap '' l.srcBox) ∧
    (∀ l ∈ ResolutionTree.leaves t,
      Function.Injective l.divCoord ∧ Function.Injective l.resCoord ∧
        Disjoint (Set.range l.divCoord) (Set.range l.resCoord) ∧
        (∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn l.chartMap (l.srcBox \ N)) ∧
        LeafPullback l ∧ LeafJacobian l) ∧
    (∀ p ∈ ResolutionTree.leafPaths (id : Params M → Params M) t, p.1.chartMap = p.2)

/-- **The edge-relational per-step invariant** (finding 1: reads `e.child` + `e.subst.runLen`).
* **case 2** — a shared divisor on the parent (`∀ g, kp ∈ support g`) AND the CHILD's new divisor
  has exponent `resRows·resCols` (worked.tex:516).
* **case 1(1)** — a parent divisor at level `J` merges: the CHILD exponent is
  `parent divExp + J₁·resCols` (`M' = M + J₁·(M^{(S+1)}−J)`; worked.tex:505–507).
* **case 1(2)** — the CHILD advances `cleared` (a new pivot). -/
def StepRel {M : Fin (L + 1) → ℕ} (n : StepData M) (e : Edge M) : Prop :=
  (e.case = StepCase.case2 →
      (∃ kp : Fin n.numDiv, ∀ g : Fin n.numGen, kp ∈ n.support g) ∧
      (∃ kc : ℕ, kc < ResolutionTree.rootNumDiv e.child ∧
        ResolutionTree.rootDivExp e.child kc = n.resRows * n.resCols)) ∧
  (e.case = StepCase.case11 →
      ∃ kp : Fin n.numDiv, n.divTilde kp = n.cleared ∧
        ∃ kc : ℕ, kc < ResolutionTree.rootNumDiv e.child ∧
          ResolutionTree.rootDivExp e.child kc = n.divExp kp + e.subst.runLen * n.resCols) ∧
  (e.case = StepCase.case12 →
      ResolutionTree.rootCleared e.child = n.cleared + 1 ∧ 0 < ResolutionTree.rootNumDiv e.child)

/-- **Full monomialisation**: each leaf's terminal divisor exponent equals `Mval` of its rank
profile, AND that profile is ADMISSIBLE (`divProfile k ∈ Adm M` — finding 4). The leaf chain is
enforced at type strength by `LeafData.bChain`. -/
def IsFullMonomialization {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : Prop :=
  ∀ l ∈ ResolutionTree.leaves t, ∀ k : Fin l.numDiv,
    l.divExp k = (Mval M (l.divProfile k)).toNat ∧ l.divProfile k ∈ Adm M

/-- **A canonical resolution** — the bundle every downstream obligation projects from. Conjoins full
monomialisation; the edge-relational `StepRel` on every parent–edge pair; the branch-rooted base
`S = J = 0`; the CoV `ChartBridge`; the exponent hooks (`minAdm` lower-bounds + is a terminal
exponent); and the LIVE attainment — `minAdm` is a divisor exponent of a leaf with a NONEMPTY source
box (finding 3, killing the empty-`srcBox` phantom). -/
def CanonicalResolution (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  IsFullMonomialization t ∧
    (∀ p ∈ ResolutionTree.stepEdges t, StepRel p.1 p.2) ∧
      (∃ (n : StepData M) (edges : List (Edge M)),
          t = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0) ∧
        ChartBridge M t ∧
          ((∀ e ∈ ResolutionTree.terminalExponents t, minAdm M ≤ e) ∧
            minAdm M ∈ ResolutionTree.terminalExponents t) ∧
          (∃ l ∈ ResolutionTree.leaves t, l.srcBox.Nonempty ∧
            minAdm M ∈ (List.finRange l.numDiv).map l.divExp)

/-! ## The construction hole + the canonical resolution -/

/-- **Monomialisation terminates into a canonical resolution** (map: `monomialization-termination`;
the ONE construction hole). Layer B; structural. The coverage/step/exponent/CoV CONTENT lives
here. -/
@[blueprint] theorem monomialization_terminates (M : Fin (L + 1) → ℕ) :
    ∃ t : ResolutionTree M, CanonicalResolution M t := by
  sorry

/-- **The canonical resolution** of `M`. A blueprint forecast (rests on the sorried
construction). -/
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

/-- **Case-step invariant** (map: `case-step-lemmas`). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem case_step_invariant (M : Fin (L + 1) → ℕ) :
    ∀ p ∈ ResolutionTree.stepEdges (resolutionOf M), StepRel p.1 p.2 :=
  (resolutionOf_spec M).2.1

/-- **Reduction layer** (map: `reduction-layer`). The regular peel: the resolution begins at the
base `S = J = 0`. STRUCTURAL (Layer-B fence). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem reduction_layer (M : Fin (L + 1) → ℕ) :
    ∃ (n : StepData M) (edges : List (Edge M)),
      resolutionOf M = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0 :=
  (resolutionOf_spec M).2.2.1

/-- **Coverage — THE HARD PART** (map: `coverage-theorem`, owned by coverage-design). The atlas
covers an UPSTAIRS-open box-neighbourhood via chart images, per-leaf injective/disjoint coords,
a.e.-injective charts, pullback, Jacobian, and the derived coherence. WITHOUT `rlct = c*`. A
projection. -/
@[blueprint] theorem coverage_theorem (M : Fin (L + 1) → ℕ) :
    ChartBridge M (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.1

/-- **Exponent-ledger bridge** (map: `exponent-ledger-bridge`). `minAdm M` is a terminal exponent
(now including `resRank`) and lower-bounds them all — so `minAdm ≤ resRank` too (ruling 2a).
Consumes `minAdm`/`Mval` verbatim. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem exponent_ledger_bridge (M : Fin (L + 1) → ℕ) :
    (∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), minAdm M ≤ e) ∧
      minAdm M ∈ ResolutionTree.terminalExponents (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.2.1

/-- **Live attainment** (finding 3): `minAdm M` is attained by a divisor exponent of a leaf with a
NONEMPTY source box — no empty-`srcBox` phantom. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem exponent_ledger_liveAttainment (M : Fin (L + 1) → ℕ) :
    ∃ l ∈ ResolutionTree.leaves (resolutionOf M), l.srcBox.Nonempty ∧
      minAdm M ∈ (List.finRange l.numDiv).map l.divExp :=
  (resolutionOf_spec M).2.2.2.2.2

/-- **Region glue** (map: `region-glue`; the ONE analytic hole). ASSEMBLY ONLY: given the CoV
bridge, the box integral is finite whenever `c'` is below half every terminal exponent (divisor
exponents AND the folded `resRank` — so the Morse-core threshold is covered) — the banked
monomial/radial reads +
`rlctAtOn_boundedUnit_localHomeomorph` on the `ψ` factor + direct monomial integration of the `β`
factor, glued over the upstairs-open finite subcover. Precondition `IsFullMonomialization`. -/
@[blueprint] theorem region_glue (M : Fin (L + 1) → ℕ)
    (hbridge : ChartBridge M (resolutionOf M)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT.Engine
