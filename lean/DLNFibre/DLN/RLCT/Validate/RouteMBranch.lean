import DLNFibre.DLN.RLCT.Validate.RouteMClassify
import DLNFibre.DLN.RLCT.Validate.Case222RouteStep

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMBranch` — the `routeStep` branch constructor (fm3, sub-2)

The generic branch-arm assembly for the general `routeStep` dispatcher (`RouteMRecursion.routeStep`),
built as a standalone building block. Given a node `(root M₀, current M)` with `hlo` (the `schurState`
precondition), a finite nonempty `cells` of pivot choices, a per-cell `codim`, and a per-cell
ROOT-anchored `PivotWitness M₀ (codim c)`, `routeStepBranch` assembles the `RouteStep.branch` with the
uniform `schurState M hlo` split (every cell shares the C1/C5 reduced-width split; the pivot CHOICE is the
`codim`/`witness`, which differs per cell).

**Honesty boundary (the trap-(iii) fence).** This constructor CONSUMES the per-cell `PivotWitness M₀` — it
does not manufacture one. The committed `PivotWitness M₀ c` (`RouteMState.lean`) certifies only
`T ∈ Adm M₀ ∧ codim = Mval M₀ T`; it carries NO realizability field, so the constructor cannot (and does
not pretend to) certify that the chart path reaches the stratum. Supplying the witnesses honestly is the
CALLER's obligation: for finite instances (`(2,2,2)`/`(3,2,3)`) the witness `T*` is `decide`-checkable
(`Case222RouteStep`); for the general node the achiever witness rides the diagonal-cascade realizability
(`T* ∈ RealizableRank M₀`, pp2 g228 — NOT yet transcribed to Core, the genuinely-new piece tracked below).
So `routeStepBranch` is the honest assembly; the realizability source is upstream, never smuggled here.

`routeStepBranch_M222` reproduces `case222_routeStep_branch` through this generic constructor — the
non-vacuity / fidelity check that the constructor generalizes the worked (2,2,2) template exactly.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The branch arm of the dispatcher** (generic assembly). At a non-leaf node `(M₀, M)` with `hlo`
(the `schurState` precondition), a finite nonempty `cells` of pivot choices, a per-cell `codim`, and a
per-cell root-anchored `PivotWitness M₀ (codim c)`, build the `RouteStep.branch` with the uniform
`schurState M hlo` split. CONSUMES the witnesses (does not manufacture them — the realizability source is
the caller's, never smuggled): this is the honest assembly that the value fold and descent ride on. -/
def routeStepBranch (M₀ M : Fin (L + 1) → ℕ)
    (hlo : ∀ s : Fin (L + 1), s.val ≤ 1 → 1 ≤ M s)
    (cells : Type) [Fintype cells] [Nonempty cells]
    (codim : cells → ℕ) (witness : (c : cells) → PivotWitness M₀ (codim c)) :
    RouteStep M₀ M :=
  .branch cells inferInstance inferInstance (fun _ => schurState M hlo) codim witness

/-- The split of every cell of `routeStepBranch` is the uniform `schurState M hlo` — the C1/C5
reduced-width split `(M₀−1, M₁−1, M₂, …)`. -/
theorem routeStepBranch_split (M₀ M : Fin (L + 1) → ℕ)
    (hlo : ∀ s : Fin (L + 1), s.val ≤ 1 → 1 ≤ M s)
    (cells : Type) [Fintype cells] [Nonempty cells]
    (codim : cells → ℕ) (witness : (c : cells) → PivotWitness M₀ (codim c)) :
    routeStepBranch M₀ M hlo cells codim witness =
      .branch cells inferInstance inferInstance (fun _ => schurState M hlo) codim witness :=
  rfl

/-! ## The (2,2,2) reproduction — `routeStepBranch` generalizes the worked template exactly

`case222_routeStep_branch` (the hand-built (2,2,2) branch term, `Case222RouteStep`) is recovered by
`routeStepBranch` with `cells = Bool`, the codim `(fun b => if b then 4 else 3)`, and the
`decide`-checked root-anchored witnesses `step1`/`step2`. Confirms the generic constructor produces the
worked template's term — the non-vacuity / fidelity check. -/

/-- The (2,2,2) per-cell witness: `true ↦ pivotWitness222_step1` (codim 4), `false ↦ step2` (codim 3). The
`decide`-checked root-anchored witnesses, supplied by the caller (the finite instance is the honest
source). -/
def witness222 : (b : Bool) → PivotWitness M222route (if b then 4 else 3) := fun b => by
  by_cases hb : b = true
  · simpa [hb] using pivotWitness222_step1
  · simp only [Bool.not_eq_true] at hb
    simpa [hb] using pivotWitness222_step2

/-- **`routeStepBranch` reproduces `case222_routeStep_branch`.** The generic branch constructor, instantiated
with `Bool` cells, the (2,2,2) codims `4`/`3`, and the root-anchored witnesses, equals the hand-built
worked-template term. The fidelity check that sub-2's constructor generalizes the (2,2,2) anchor exactly. -/
theorem routeStepBranch_M222 :
    routeStepBranch M222route M222route M222_hlo Bool (fun b => if b then 4 else 3) witness222
      = case222_routeStep_branch :=
  rfl

end DLNFibre.DLN.RLCT
