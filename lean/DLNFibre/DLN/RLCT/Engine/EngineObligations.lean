import DLNFibre.DLN.RLCT.Engine.ResolutionTree
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineObligations` — the sorried step-lemmas of the engine

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.** The transform-only Aoyagi engine, decomposed into the obligations of the map's
`engine-route`. Each
theorem below is a `@[blueprint]` forecast (a named, typed hole) carrying its map-node id; the tides
fill them one at a time after route adoption. **Statement detail is deliberately loose where marked;
the fork-level SHAPE (what couples to what, what quantifies over what) is the forecast.**

The sole output the engine owes upstream is `RouteMBoxThresholdFinite M`
(`Validate/RouteMBoxReduction.lean`); the composition into it is `Engine.EngineDriver`. The chain,
in dependency order:

* `monomialization_terminates` — a finite full-monomialisation resolution exists (map:
  `monomialization-termination`), providing the canonical `resolutionOf M`;
* `case_step_invariant` — every blow-up node obeys its Case 1(1)/1(2)/2 exponent recurrence and its
  sharing map (map: `case-step-lemmas`);
* `coverage_theorem` — THE HARD PART: the atlas covers the zero-locus box-neighbourhood (map:
  `coverage-theorem`);
* `reduction_layer` — the regular peel bounds the box integral by the resolved-core atlas integral
  (map: `reduction-layer`);
* `exponent_ledger_bridge` — the terminal divisor exponents' minimum is the banked `minAdm M` (map:
  `exponent-ledger-bridge`; consumes `minAdm`/`Mval` verbatim, never re-derives);
* `region_glue` — a finite atlas of monomial charts, each finite below its ratio, is finite below
  the minimum ratio (map: `region-glue`).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Supporting forecast definitions (loose detail; shape-locked) -/

/-- **Chart-local monomial integral** (forecast integrand). Over the unit cube in the leaf's
exceptional coordinates, the product of `u_k` raised to the monomial-rule exponent
`(divExp k − 1) − 2·c'` — Jacobian power `divExp k − 1`, loss vanishing to order `2` along each
`u_k = 0` (`aoyagi-2023-worked.tex` § Jacobian: ratio `= divExp k / 2`). The exact *coupled*
integrand (the shared `bᵢ` monomials) is the tide's; at a normal-crossing leaf it separates to this
product form. -/
@[blueprint] noncomputable def monomialChartIntegral (l : LeafData (L := L) M) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ u : Fin l.numDiv → ℝ in Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1),
    ∏ k : Fin l.numDiv, ENNReal.ofReal ((u k) ^ (((l.divExp k : ℝ) - 1) - 2 * c'))

/-- **The resolved-core atlas integral**: the sum of the chart-local monomial integrals over the
resolution's leaves — the value the regular peel (`reduction_layer`) reduces the box integral to. -/
@[blueprint] noncomputable def residualBoxIntegral (M : Fin (L + 1) → ℕ)
    (t : ResolutionTree M) (c' : ℝ) : ℝ≥0∞ :=
  ((ResolutionTree.leaves t).map (fun l => monomialChartIntegral l c')).sum

/-- **The atlas covers** the box-neighbourhood of the zero locus: every box parameter at which the
loss vanishes lies in some leaf chart's domain. (Coverage's set-level content; the finite-subcover /
measure step rides on it in `region_glue`.) -/
@[blueprint] def ChartsCover (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0}
    ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartDom

/-- **The per-step invariant** a valid resolution node satisfies. Case 2 introduces a divisor whose
exponent is the residual codimension `(M(S)−J)(M(S+1)−J) = resRows·resCols` and which divides every
residual generator (the sharing that flattening loses — `g-coupled-binding-334.py`). Case 1(1) is
the exponent-merge at clearing level `J`. (Shape-locked; the ideal-preservation identity is the
tide's.) -/
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
§ blow-up). -/
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
monomial Jacobian (Aoyagi pp.15–22). -/
@[blueprint] theorem case_step_invariant (M : Fin (L + 1) → ℕ) :
    ∀ n ∈ ResolutionTree.nodes (resolutionOf M), StepInvariant n := by
  sorry

/-- **Coverage — THE HARD PART** (map: `coverage-theorem`). The canonical resolution's chart atlas
covers a box-neighbourhood of the zero locus, and (implicitly, via the terminal exponents read by
`exponent_ledger_bridge`) no untracked chart carries a smaller ratio. Aoyagi *asserts* this ("by a
blow-up process", p.22); we reconstruct it — WITHOUT invoking `rlct = c*` (circularity guard).
Design-first, decorrelated. -/
@[blueprint] theorem coverage_theorem (M : Fin (L + 1) → ℕ) :
    ChartsCover M (resolutionOf M) := by
  sorry

/-- **Reduction layer** (map: `reduction-layer`). Lemma 2 / Theorem 3: the regular peel
(`P₁ (∏A) P₂ = diag(C₁, ∏C)`, `C₁` regular) bounds the layer-product box integral by the
resolved-core atlas integral — the peeled regular directions contribute a finite factor.
Transcription over the banked shear/pivot analogues. -/
@[blueprint] theorem reduction_layer (M : Fin (L + 1) → ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral M c' 1 ≤ residualBoxIntegral M (resolutionOf M) c' := by
  sorry

/-- **Exponent-ledger bridge** (map: `exponent-ledger-bridge`). The minimum of the resolution's
terminal divisor exponents is the banked `minAdm M`: `minAdm` is a terminal exponent and
lower-bounds them all. Consumes `minAdm`/`Mval` verbatim (via `IsFullMonomialization`); never
re-derives the
arithmetic. -/
@[blueprint] theorem exponent_ledger_bridge (M : Fin (L + 1) → ℕ) :
    (∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), minAdm M ≤ e) ∧
      minAdm M ∈ ResolutionTree.terminalExponents (resolutionOf M) := by
  sorry

/-- **Region glue** (map: `region-glue`). Given coverage, the resolved-core atlas integral is finite
whenever `c'` is below half every terminal divisor exponent — a finite atlas of monomial charts,
each finite below its ratio `divExp k / 2` (the banked monomial reads), sums finite. The
finite-subcover
over the box (`S1Cover`, `RouteMCoverLemmas`) and the deepest-point/IH domination live here. -/
@[blueprint] theorem region_glue (M : Fin (L + 1) → ℕ)
    (hcov : ChartsCover M (resolutionOf M)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
    residualBoxIntegral M (resolutionOf M) c' < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT.Engine
