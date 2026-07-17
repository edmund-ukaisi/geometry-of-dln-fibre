import DLNFibre.DLN.RLCT.Engine.ResolutionTree
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineObligations` — the sorried step-lemmas of the engine

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.** The transform-only Aoyagi engine, decomposed into the obligations of the map's
`engine-route`. Each theorem below is a `@[blueprint]` forecast (a named, typed hole) carrying its
map-node id; the tides fill them one at a time after route adoption. **Statement detail is
deliberately loose where marked; the fork-level SHAPE (what couples to what, what quantifies over
what) is the forecast.**

**Layer discipline (compass, convening #1):** Layer B (reduction / tree / case-steps / exponent
ledger) owes *charts + invariant preservation + exponent ledger* and delegates convergence entirely
to Layer D's banked monomial reads — **a Layer-B lemma that integrates anything is off-contract.**
Only `region_glue` (the assembly) and `coverage_theorem`/theorem4 (Layer C) touch integrals. So
`reduction_layer` below is STRUCTURAL (it integrates nothing); `region_glue` is ASSEMBLY-only (the
non-deepest reduction is theorem4-localization's, owned by coverage-design — kept acyclic).

The sole output the engine owes upstream is `RouteMBoxThresholdFinite M`
(`Validate/RouteMBoxReduction.lean`); the composition into it is `Engine.EngineDriver`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Supporting forecast predicates (loose detail; shape-locked) -/

/-- **The atlas covers** the box-neighbourhood of the zero locus: every box parameter at which the
loss vanishes lies in some leaf chart's domain. (Coverage's set-level content; the finite-subcover /
measure step rides on it in `region_glue`.) -/
@[blueprint] def ChartsCover (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0}
    ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartDom

/-- **The per-step invariant** a valid resolution node satisfies. Case 2 introduces a divisor whose
exponent is the residual codimension `(M(S)−J)(M(S+1)−J) = resRows·resCols` and which divides every
residual generator (the sharing that flattening loses — `g-coupled-binding-334.py`; the coupling is
carried by the TYPED `support : Gen → Finset DivVar` field, so a per-generator-multiplicity flatten
is a type error, not merely a battery failure). Case 1(1) is the exponent-merge at clearing level
`J`. (Shape-locked; the ideal-preservation identity is the tide's.) -/
@[blueprint] def StepInvariant {M : Fin (L + 1) → ℕ} (n : StepData M) : Prop :=
  (n.case = StepCase.case2 → ∃ k : Fin n.numDiv,
      n.divExp k = n.resRows * n.resCols ∧ ∀ g : Fin n.numGen, k ∈ n.support g) ∧
  (n.case = StepCase.case11 → ∃ k : Fin n.numDiv, n.divTilde k = n.cleared)

/-- **Full monomialisation**: at every leaf, each terminal divisor's accumulated exponent equals
`Mval` of its rank profile (Aoyagi p.22: `M_{s,k} = Mval(t_{s,k})`) — the recursion has reached the
`S = L+1` normal-crossing diagonal. -/
@[blueprint] def IsFullMonomialization {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : Prop :=
  ∀ l ∈ ResolutionTree.leaves t, ∀ k : Fin l.numDiv,
    l.divExp k = (Mval M (l.divProfile k)).toNat

/-! ## The obligations -/

/-- **Monomialisation terminates** (map: `monomialization-termination`). For every width vector a
finite resolution tree exists whose leaves are full monomialisations — the double induction
terminates at `S = L+1` in the diagonal `⟨diag(b₁…b_{M(L+1)})⟩` (`aoyagi-2023-worked.tex`
§ blow-up). Layer B; structural (integrates nothing). -/
@[blueprint] theorem monomialization_terminates (M : Fin (L + 1) → ℕ) :
    ∃ t : ResolutionTree M, IsFullMonomialization t := by
  sorry

/-- **The canonical resolution** of `M` — the tree furnished by `monomialization_terminates`. A
blueprint forecast (it rests on the sorried existence). -/
@[blueprint] noncomputable def resolutionOf (M : Fin (L + 1) → ℕ) : ResolutionTree M :=
  (monomialization_terminates M).choose

/-- The canonical resolution is a full monomialisation. -/
@[blueprint] theorem resolutionOf_spec (M : Fin (L + 1) → ℕ) :
    IsFullMonomialization (resolutionOf M) :=
  (monomialization_terminates M).choose_spec

/-- **Case-step invariant** (map: `case-step-lemmas`). Every blow-up node of the canonical
resolution satisfies its Case 1(1)/1(2)/2 exponent recurrence and sharing constraint — the unipotent
CoV + blow-up substitution preserves the inductive invariant `diag(b)·[E_J 0; 0 D_J]·(rest)` with a
monomial Jacobian (Aoyagi pp.15–22). Layer B; structural (integrates nothing). Consumes the typed
sharing field `support` (via `StepInvariant`). -/
@[blueprint] theorem case_step_invariant (M : Fin (L + 1) → ℕ) :
    ∀ n ∈ ResolutionTree.nodes (resolutionOf M), StepInvariant n := by
  sorry

/-- **Reduction layer** (map: `reduction-layer`). Lemma 2 / Theorem 3: the regular peel
(`P₁ (∏A) P₂ = diag(C₁, ∏C)`, `C₁` regular) isolates the reduced core `D₀ = ∏C`, from which the
resolution tree recurses — so the canonical resolution *begins at the base of the invariant*
(`S = J = 0`). STRUCTURAL: Layer B, integrates nothing (the Layer-B fence). Transcription over the
banked shear/pivot analogues; the residual-block dimensions are loose detail here. -/
@[blueprint] theorem reduction_layer (M : Fin (L + 1) → ℕ) :
    ∃ (n : StepData M) (charts : List (ResolutionTree M)),
      resolutionOf M = ResolutionTree.branch n charts ∧ n.layer = 0 ∧ n.cleared = 0 := by
  sorry

/-- **Coverage — THE HARD PART** (map: `coverage-theorem`, owned by coverage-design). The canonical
resolution's chart atlas covers a box-neighbourhood of the zero locus, and (via the terminal
exponents read by `exponent_ledger_bridge`) no untracked chart carries a smaller ratio — a UNIVERSAL
claim (the decorrelated exhaustiveness hunt precedes `established`). Aoyagi *asserts* this ("by a
blow-up process", p.22); we reconstruct it, WITHOUT invoking `rlct = c*` (circularity guard).
Non-deepest cells are theorem4-localization's; here only the *tracked* cells. -/
@[blueprint] theorem coverage_theorem (M : Fin (L + 1) → ℕ) :
    ChartsCover M (resolutionOf M) := by
  sorry

/-- **Exponent-ledger bridge** (map: `exponent-ledger-bridge`). The minimum of the resolution's
terminal divisor exponents is the banked `minAdm M`: `minAdm` is a terminal exponent and
lower-bounds them all. Consumes `minAdm`/`Mval` verbatim (via `IsFullMonomialization`); never
re-derives the arithmetic. Layer B ↔ Layer D bridge; integrates nothing. -/
@[blueprint] theorem exponent_ledger_bridge (M : Fin (L + 1) → ℕ) :
    (∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), minAdm M ≤ e) ∧
      minAdm M ∈ ResolutionTree.terminalExponents (resolutionOf M) := by
  sorry

/-- **Region glue** (map: `region-glue`). ASSEMBLY ONLY: given coverage, the box integral is finite
whenever `c'` is below half every terminal divisor exponent — a finite subcover of the box
(`S1Cover`, `RouteMCoverLemmas`, null disposals) of monomial charts, each finite below its ratio
`divExp k / 2` (the banked Layer-D monomial reads), sums finite. The *non-deepest* reduction is
theorem4-localization's (owned by coverage-design; kept acyclic — no coverage↔theorem4 cycle here).
Region-uniformity is UNWITNESSED — the two commissioned battery witnesses (glue-level lossy-vs-exact;
pivot co-null) precede this tide. -/
@[blueprint] theorem region_glue (M : Fin (L + 1) → ℕ)
    (hcov : ChartsCover M (resolutionOf M)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT.Engine
