import DLNFibre.DLN.RLCT.Engine.ResolutionTree
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineObligations` — the engine's obligations, bundled

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.** The transform-only Aoyagi engine, decomposed into the obligations of the map's
`engine-route`. **Statement detail is deliberately loose where marked; the fork-level SHAPE is the
forecast.**

**The bundling (review round 1 repair).** A naked `resolutionOf := (∃ t, IsFullMonomialization
t).choose` UNDER-DETERMINES the tree — a junk leaf (`numDiv = 0`) satisfies `IsFullMonomialization`
vacuously yet has empty `terminalExponents`, so the ledger/coverage/reduction obligations are not
dischargeable against it (C2). The fix: one predicate `CanonicalResolution` conjoining every property
the downstream obligations need; `monomialization_terminates` produces a tree satisfying it;
`resolutionOf` picks that tree; and each obligation is a PROJECTION of `resolutionOf_spec`. The single
construction hole is `monomialization_terminates`; the single analytic hole is `region_glue`.

**Layer discipline (compass, convening #1):** Layer B (reduction / tree / case-steps / exponent
ledger) delegates convergence entirely to Layer D's banked monomial reads — **a Layer-B lemma that
integrates anything is off-contract.** Only `region_glue` (the assembly) touches integrals;
`reduction_layer`/`case_step_invariant`/`exponent_ledger_bridge` are structural. The non-deepest
reduction is theorem4-localization's (owned by coverage-design) — kept acyclic (no coverage↔theorem4
edge here).

The sole output the engine owes upstream is `RouteMBoxThresholdFinite M`
(`Validate/RouteMBoxReduction.lean`); the composition into it is `Engine.EngineDriver`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Supporting forecast predicates (loose detail; shape-locked) -/

/-- **The atlas covers a NEIGHBOURHOOD** of the zero locus (review round 1, M3). Not merely the
measure-zero locus `{frobSq = 0}` itself, but an OPEN set `U` around it, contained in the union of
the (open) leaf chart domains: `locus ⊆ U ⊆ ⋃ chartDom`, `U` and each `chartDom` open. This is the
honest covering statement — a resolution atlas must cover a neighbourhood for the
finite-subcover/domination assembly to fire. -/
def ChartsCover (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  (∀ l ∈ ResolutionTree.leaves t, IsOpen l.chartDom) ∧
    ∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartDom

/-- **The per-step invariant** a valid resolution node satisfies (Aoyagi pp.15–22 Cases
1(1)/1(2)/2).
* **Case 2** introduces a divisor of exponent `(M(S)−J)(M(S+1)−J) = resRows·resCols` dividing every
  residual generator (the sharing that flattening loses — `g-coupled-binding-334.py`; carried by the
  TYPED `support` field, so a per-generator-multiplicity flatten is a type error).
* **Case 1(1)** is the exponent-merge into an existing divisor at clearing level `J`.
* **Case 1(2)** introduces a NEW pivot divisor `u_{S,J+1}` (clearing level `J`) that enters the
  monomial vector (appears in some `bᵢ`) and advances `J` — the new-pivot branch (review round 1,
  M6).
(Shape-locked; the ideal-preservation identity is the tide's.) -/
def StepInvariant {M : Fin (L + 1) → ℕ} (n : StepData M) : Prop :=
  (n.case = StepCase.case2 → ∃ k : Fin n.numDiv,
      n.divExp k = n.resRows * n.resCols ∧ ∀ g : Fin n.numGen, k ∈ n.support g) ∧
  (n.case = StepCase.case11 → ∃ k : Fin n.numDiv, n.divTilde k = n.cleared) ∧
  (n.case = StepCase.case12 → ∃ k : Fin n.numDiv,
      n.divTilde k = n.cleared ∧ ∃ i : Fin n.numB, 0 < n.bExp i k)

/-- **Full monomialisation**: at every leaf, each terminal divisor's accumulated exponent equals
`Mval` of its rank profile (Aoyagi p.22: `M_{s,k} = Mval(t_{s,k})`). The leaf divisibility chain is
enforced at type strength by `LeafData.bChain` (review round 1, C1) — this predicate need only pin
the exponents to `Mval`. -/
def IsFullMonomialization {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : Prop :=
  ∀ l ∈ ResolutionTree.leaves t, ∀ k : Fin l.numDiv,
    l.divExp k = (Mval M (l.divProfile k)).toNat

/-- **A canonical resolution** — the bundle every downstream obligation consumes (review round 1,
C2/M3/M5/M6). Conjoins: (1) full monomialisation (`Mval` exponents; chain leaves via
`LeafData.bChain`); (2) the per-node Case invariant everywhere (`case_step_invariant`); (3) the
branch-rooted base of the invariant `S = J = 0` (`reduction_layer`); (4) neighbourhood coverage
(`coverage_theorem`); (5) the exponent-ledger hooks — `minAdm M` is the minimum of the terminal
exponents (`exponent_ledger_bridge`; this clause is FALSE for a junk/empty leaf, killing the
underdetermination). -/
def CanonicalResolution (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  IsFullMonomialization t ∧
    (∀ n ∈ ResolutionTree.nodes t, StepInvariant n) ∧
      (∃ (n : StepData M) (charts : List (ResolutionTree M)),
          t = ResolutionTree.branch n charts ∧ n.layer = 0 ∧ n.cleared = 0) ∧
        ChartsCover M t ∧
          ((∀ e ∈ ResolutionTree.terminalExponents t, minAdm M ≤ e) ∧
            minAdm M ∈ ResolutionTree.terminalExponents t)

/-! ## The construction hole + the canonical resolution -/

/-- **Monomialisation terminates into a canonical resolution** (map: `monomialization-termination`;
the ONE construction hole). For every width vector a finite resolution tree exists satisfying
`CanonicalResolution` — the double induction terminates at `S = L+1` in the diagonal
`⟨diag(b₁…b_{M(L+1)})⟩` and the resulting atlas carries every downstream property. Layer B;
structural (integrates nothing). This is where the coverage/step/exponent CONTENT lives; the
obligations below are its projections. -/
@[blueprint] theorem monomialization_terminates (M : Fin (L + 1) → ℕ) :
    ∃ t : ResolutionTree M, CanonicalResolution M t := by
  sorry

/-- **The canonical resolution** of `M`. A blueprint forecast (rests on the sorried construction). -/
@[blueprint] noncomputable def resolutionOf (M : Fin (L + 1) → ℕ) : ResolutionTree M :=
  (monomialization_terminates M).choose

/-- The canonical resolution satisfies the full bundle — the spec every obligation projects from. -/
@[blueprint] theorem resolutionOf_spec (M : Fin (L + 1) → ℕ) :
    CanonicalResolution M (resolutionOf M) :=
  (monomialization_terminates M).choose_spec

/-- The canonical resolution is a full monomialisation (chain leaves; `Mval` exponents) — the
load-bearing precondition of `region_glue`'s separated leaf integrand (cert-d3 A1). -/
@[blueprint] theorem resolutionOf_isFullMonomialization (M : Fin (L + 1) → ℕ) :
    IsFullMonomialization (resolutionOf M) :=
  (resolutionOf_spec M).1

/-! ## The obligations (projections of the bundle) + the analytic hole -/

/-- **Case-step invariant** (map: `case-step-lemmas`). Every blow-up node of the canonical
resolution satisfies its Case 1(1)/1(2)/2 exponent recurrence and sharing constraint. A projection
of `resolutionOf_spec`; the content lives in `monomialization_terminates`. Consumes the typed
sharing field `support` (via `StepInvariant`). -/
@[blueprint] theorem case_step_invariant (M : Fin (L + 1) → ℕ) :
    ∀ n ∈ ResolutionTree.nodes (resolutionOf M), StepInvariant n :=
  (resolutionOf_spec M).2.1

/-- **Reduction layer** (map: `reduction-layer`). Lemma 2 / Theorem 3: the regular peel isolates the
reduced core `D₀ = ∏C`, so the canonical resolution begins at the base of the invariant `S = J = 0`.
STRUCTURAL (Layer-B fence: integrates nothing). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem reduction_layer (M : Fin (L + 1) → ℕ) :
    ∃ (n : StepData M) (charts : List (ResolutionTree M)),
      resolutionOf M = ResolutionTree.branch n charts ∧ n.layer = 0 ∧ n.cleared = 0 :=
  (resolutionOf_spec M).2.2.1

/-- **Coverage — THE HARD PART** (map: `coverage-theorem`, owned by coverage-design). The canonical
resolution's chart atlas covers a box-NEIGHBOURHOOD of the zero locus (no untracked chart carries a
smaller ratio — the UNIVERSAL claim gated by the exhaustiveness hunt). WITHOUT `rlct = c*`
(circularity guard). A projection of `resolutionOf_spec`; the covering CONTENT is discharged inside
`monomialization_terminates`. Non-deepest cells are theorem4-localization's. -/
@[blueprint] theorem coverage_theorem (M : Fin (L + 1) → ℕ) :
    ChartsCover M (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.1

/-- **Exponent-ledger bridge** (map: `exponent-ledger-bridge`). `minAdm M` is the minimum of the
resolution's terminal divisor exponents: it is a terminal exponent and lower-bounds them all.
Consumes `minAdm`/`Mval` verbatim (via `IsFullMonomialization`); never re-derives the arithmetic. A
projection of `resolutionOf_spec`. Integrates nothing. -/
@[blueprint] theorem exponent_ledger_bridge (M : Fin (L + 1) → ℕ) :
    (∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), minAdm M ≤ e) ∧
      minAdm M ∈ ResolutionTree.terminalExponents (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.2

/-- **Region glue** (map: `region-glue`; the ONE analytic hole). ASSEMBLY ONLY: given coverage, the
box integral is finite whenever `c'` is below half every terminal divisor exponent — a finite
subcover of the box (`S1Cover`, `RouteMCoverLemmas`, null disposals) of monomial charts, each finite
below its ratio `divExp k / 2` (the banked Layer-D monomial reads), sums finite. Its load-bearing
precondition is `IsFullMonomialization` (`resolutionOf_isFullMonomialization`): on a chain leaf
`∑ bᵢ² = b₁²·unit`, so the SEPARATED per-divisor read is exact — no coupled integrand, no consulting
`support` (cert-d3 A1, `g-leaf-chain-separation.py`). The non-deepest reduction is
theorem4-localization's (acyclic). Region-uniformity UNWITNESSED — the two commissioned battery
witnesses (glue-level lossy-vs-exact; pivot co-null) precede this tide. -/
@[blueprint] theorem region_glue (M : Fin (L + 1) → ℕ)
    (hcov : ChartsCover M (resolutionOf M)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  sorry

/-! ## Non-vacuity witnesses (review round 1, MINOR-8) -/

/-- A genuine Case-2 node: residual `1×1`, one divisor of exponent `1 = resRows·resCols` dividing
the one generator. -/
def witNode {M : Fin (L + 1) → ℕ} : StepData M where
  layer := 0; cleared := 0; case := StepCase.case2; resRows := 1; resCols := 1
  numDiv := 1; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun _ => 1; divTilde := fun _ => 0; numGen := 1; support := fun _ => {0}

/-- **Non-vacuity**: the Case-2 witness node satisfies `StepInvariant` (its case-2 clause is real —
`divExp 0 = 1 = 1·1` and `0 ∈ support 0`; the case-1 clauses are vacuous). -/
theorem witNode_stepInvariant {M : Fin (L + 1) → ℕ} : StepInvariant (witNode (M := M)) := by
  unfold StepInvariant witNode
  refine ⟨fun _ => ⟨0, rfl, fun _ => Finset.mem_singleton_self 0⟩, ?_, ?_⟩
  · intro h; simp at h
  · intro h; simp at h

/-- A minimal terminal leaf (one divisor, one monomial; a chain leaf). -/
def witLeaf {M : Fin (L + 1) → ℕ} : LeafData M where
  numDiv := 1; divExp := fun _ => 1; divProfile := fun _ _ => 0
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _; chartDom := Set.univ

/-- A **nontrivial tree**: a genuine `branch` node (not a bare leaf) over one chart — the carrier is
inhabited by a branching value carrying the sharing data (`witNode.support`), not only by leaves. Its
well-typed existence is the non-vacuity witness for the tree layer. -/
def witTree {M : Fin (L + 1) → ℕ} : ResolutionTree M :=
  ResolutionTree.branch witNode [ResolutionTree.leaf witLeaf]

end DLNFibre.DLN.RLCT.Engine
