import DLNFibre.DLN.RLCT.Engine.ResolutionTree
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineObligations` — the engine's obligations (edge-labelled,
ChartBridge)

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.**
The transform-only Aoyagi engine's obligations over the council-adopted EDGE-LABELLED carrier, with
the CoV `ChartBridge` (Q5 route (b), fork 8) replacing the refuted abstract `ChartsCover`.
**Statement
detail is loose where marked; the fork-level SHAPE is the forecast.**

`CanonicalResolution = IsFullMonomialization ∧ StepRel-everywhere ∧ branch-rooted ∧ ChartBridge ∧
(exponent hooks + tStar attainment)`. `ChartBridge` = UPSTAIRS image cover + per-leaf InjOn +
`LeafPullback` + `LeafJacobian` + the **chartMap-derived coherence** (each leaf's `chartMap` = the
fold
of its root→leaf edge substitutions — so `LeafPullback`/`LeafJacobian` are proved compositionally,
not
against a free map). Charts are self-maps of `Params M` (normed/findim/Haar, banked
`ParamsFlatLinear`); `LeafJacobian` is the transport-hypothesis form (`HasFDerivAt` + `|det Dφ| = ∏
u^{divExp−1} · unit`, the divisor coords read via `paramsEquivFlat`), consumed by `region_glue` via
`rlctAtOn_boundedUnit_localHomeomorph` + the scaling bridge. **Layer-B fence: only `region_glue`
integrates.** The two holes are `monomialization_terminates` + `region_glue`.
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
(∏ u²) · residualCore` — the divisor monomial `∏ (paramsEquivFlat w (divCoord k))²` times a
`residualCore` squeezed between positive multiples of the base form (`‖z‖²` Morse core or unit `1`).
-/
def LeafPullback (l : LeafData (L := L) M) : Prop :=
  ∃ (residualCore : Params M → ℝ) (lo hi : ℝ), 0 < lo ∧
    ∀ w ∈ l.srcBox,
      frobSq (prod M (l.chartMap w))
          = (∏ k : Fin l.numDiv, (paramsEquivFlat M w (l.divCoord k)) ^ 2) * residualCore w ∧
      lo * residualBaseForm l w ≤ residualCore w ∧ residualCore w ≤ hi * residualBaseForm l w

/-- **The Jacobian ledger** (cert-bridge-design (J); Q5 route (b), fork 8 — PINNED). The chart is a
self-map of `Params M` with a derivative `Dφ w` (existential — no derivative field is stored as
data);
its determinant is the monomial-Jacobian ledger times a positive-bounded unit:
`|det Dφ| = ∏ (paramsEquivFlat w (divCoord k))^{divExp k − 1} · jacUnit`. Exactly the datum
`region_glue`
feeds to `rlctAtOn_boundedUnit_localHomeomorph` (strip the unit) + the scaling bridge (the
monomial). -/
def LeafJacobian (l : LeafData (L := L) M) : Prop :=
  ∃ (Dφ : Params M → (Params M →L[ℝ] Params M)) (lo hi : ℝ), 0 < lo ∧
    ∀ w ∈ l.srcBox, HasFDerivAt l.chartMap (Dφ w) w ∧
      ∃ jacUnit : ℝ, lo ≤ jacUnit ∧ jacUnit ≤ hi ∧
        |(Dφ w).det|
          = (∏ k : Fin l.numDiv, (paramsEquivFlat M w (l.divCoord k)) ^ (l.divExp k - 1)) * jacUnit

/-- **The CoV bridge** (fork 8): the atlas covers an UPSTAIRS-open neighbourhood of the zero locus
via
chart IMAGES; every leaf chart is injective with a valid pullback + Jacobian; and each leaf's
`chartMap` is the DERIVED fold of its root→leaf edge substitutions (coherence — closes the free-map
gap). -/
def ChartBridge (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  (∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartMap '' l.srcBox) ∧
    (∀ l ∈ ResolutionTree.leaves t,
      Set.InjOn l.chartMap l.srcBox ∧ LeafPullback l ∧ LeafJacobian l) ∧
    (∀ p ∈ ResolutionTree.leafPaths (id : Params M → Params M) t, p.1.chartMap = p.2)

/-- **The edge-relational per-step invariant** (council: case-keyed identities). case 2: a divisor
of
exponent `resRows·resCols` dividing EVERY residual generator (shared-δ, via `n.support`); case 1(1):
the exponent-merge at level `J`; case 1(2): a new pivot at level `J` entering the monomial vector.
-/
def StepRel {M : Fin (L + 1) → ℕ} (n : StepData M) (e : Edge M) : Prop :=
  (e.case = StepCase.case2 → ∃ k : Fin n.numDiv,
      n.divExp k = n.resRows * n.resCols ∧ ∀ g : Fin n.numGen, k ∈ n.support g) ∧
  (e.case = StepCase.case11 → ∃ k : Fin n.numDiv, n.divTilde k = n.cleared) ∧
  (e.case = StepCase.case12 → ∃ k : Fin n.numDiv,
      n.divTilde k = n.cleared ∧ ∃ i : Fin n.numB, 0 < n.bExp i k)

/-- **Full monomialisation**: each leaf's terminal divisor exponent equals `Mval` of its rank
profile
(Aoyagi p.22). The leaf chain is enforced at type strength by `LeafData.bChain`. -/
def IsFullMonomialization {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : Prop :=
  ∀ l ∈ ResolutionTree.leaves t, ∀ k : Fin l.numDiv,
    l.divExp k = (Mval M (l.divProfile k)).toNat

/-- **A canonical resolution** — the bundle every downstream obligation projects from. Conjoins full
monomialisation; the edge-relational `StepRel` on every parent–edge pair; the branch-rooted base
`S = J = 0`; the CoV `ChartBridge`; and the exponent hooks — `minAdm M` is an emitted terminal
exponent
(attainment by a leaf on the atlas) and lower-bounds them all. -/
def CanonicalResolution (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  IsFullMonomialization t ∧
    (∀ p ∈ ResolutionTree.stepEdges t, StepRel p.1 p.2) ∧
      (∃ (n : StepData M) (edges : List (Edge M)),
          t = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0) ∧
        ChartBridge M t ∧
          ((∀ e ∈ ResolutionTree.terminalExponents t, minAdm M ≤ e) ∧
            minAdm M ∈ ResolutionTree.terminalExponents t)

/-! ## The construction hole + the canonical resolution -/

/-- **Monomialisation terminates into a canonical resolution** (map: `monomialization-termination`;
the ONE construction hole). Layer B; structural. The coverage/step/exponent/CoV CONTENT lives here.
-/
@[blueprint] theorem monomialization_terminates (M : Fin (L + 1) → ℕ) :
    ∃ t : ResolutionTree M, CanonicalResolution M t := by
  sorry

/-- **The canonical resolution** of `M`. A blueprint forecast (rests on the sorried construction).
-/
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
base
`S = J = 0`. STRUCTURAL (Layer-B fence). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem reduction_layer (M : Fin (L + 1) → ℕ) :
    ∃ (n : StepData M) (edges : List (Edge M)),
      resolutionOf M = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0 :=
  (resolutionOf_spec M).2.2.1

/-- **Coverage — THE HARD PART** (map: `coverage-theorem`, owned by coverage-design). The atlas
covers
an UPSTAIRS-open box-neighbourhood via chart images, per-leaf InjOn + pullback + Jacobian + the
derived
coherence. WITHOUT `rlct = c*`. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem coverage_theorem (M : Fin (L + 1) → ℕ) :
    ChartBridge M (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.1

/-- **Exponent-ledger bridge** (map: `exponent-ledger-bridge`). `minAdm M` is the minimum of the
resolution's terminal exponents (attained by an emitted leaf). Consumes `minAdm`/`Mval` verbatim. -/
@[blueprint] theorem exponent_ledger_bridge (M : Fin (L + 1) → ℕ) :
    (∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), minAdm M ≤ e) ∧
      minAdm M ∈ ResolutionTree.terminalExponents (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.2

/-- **Region glue** (map: `region-glue`; the ONE analytic hole). ASSEMBLY ONLY: given the CoV
bridge,
the box integral is finite whenever `c'` is below half every terminal divisor exponent — the banked
monomial/radial reads + `rlctAtOn_boundedUnit_localHomeomorph` (strips the Jacobian unit) + the
scaling bridge, glued over the upstairs-open finite subcover. Precondition `IsFullMonomialization`.
-/
@[blueprint] theorem region_glue (M : Fin (L + 1) → ℕ)
    (hbridge : ChartBridge M (resolutionOf M)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT.Engine
