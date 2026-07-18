import DLNFibre.DLN.RLCT.Engine.EngineDefs
import Mathlib.Data.Prod.Lex

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineConstruction` — the construction's termination spine (rung 2)

**Blueprint spine: statements are forecasts; churn is normal.** The double-induction that builds the
resolution tree (the `monomialization_terminates` hole) runs on a lean carrier `ConState` and is
proven to terminate by a lex-triple measure `μ = (L+1−S, layerCap−J, pendingCount)` on the lex
product `ℕ ×ₗ ℕ ×ₗ ℕ`.
This module pins the well-founded machinery BEFORE the recursion body: the carrier, its invariant,
the measure, and the well-founded relation — mirroring the banked `RouteMState` idiom
(`ℕ ×ₗ ℕ ×ₗ ℕ`, `toLex` nesting, `InvImage.wf _ wellFounded_lt`).

The carrier stores ONLY what the measure reads: the layer `S`, the cleared-pivot count `J`, and the
current divisor ledger (count + per-divisor exponent `M_{s,k}` and clearing level `t̃_{s,k}`).
DERIVABLE data (`resRows`/`resCols`/`numB`/`runLen`/`depth`/`minAdm`) is NOT stored — it is computed
from `M`, `S`, `J`. Distinct from the tree-node `StepData` (which materialises the derivable fields
for the certificate); `ConState` is the recursion carrier only.

Per-case descent (rung 2B) lives below the measure: a case-1(1) merge drops component 3
(`pendingCount`); a case-1(2)/case-2 step drops component 2 (`J` advances by one); a layer rollover
drops component 1 (`S` advances). No case decreases NOTHING — the termination kill-condition.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ}

/-! ## The termination carrier + invariant -/

/-- **The construction's termination carrier** (rung 2): the double-induction state stripped to what
the measure reads. `layer` is `S`, `cleared` is `J`, and `(numDiv, divExp, divTilde)` is the current
exceptional-divisor ledger (`M_{s,k}` and `t̃_{s,k}`). No derivable field is stored. -/
structure ConState where
  /-- The layer index `S`. -/
  layer : ℕ
  /-- The count `J` of unit pivots cleared in the current layer. -/
  cleared : ℕ
  /-- Number of exceptional divisors currently in scope. -/
  numDiv : ℕ
  /-- The per-divisor exponent ledger `M_{s,k}`. -/
  divExp : Fin numDiv → ℕ
  /-- The per-divisor clearing level `t̃_{s,k}`. -/
  divTilde : Fin numDiv → ℕ

/-- The within-layer ceiling on `J` (`cleared`): the total width `∑ M`, a fixed upper bound on the
cleared count in any layer (`J ≤ M(S) ≤ ∑ M`, and `J` resets to `0` at a rollover). Used as μ's 2nd
lex component's ceiling so `layerCap − J` strictly drops when `J` advances. -/
def layerCap (M : Fin (L + 1) → ℕ) : ℕ := ∑ i, M i

/-- **The pending-divisor count**: divisors whose clearing level exceeds the current cleared count
(`t̃_k > J`). μ's third lex component. A case-1(1) merge moves its target divisor's `t̃` down to
`J`, so this drops by one; the other cases leave it dominated by a strict drop in a higher
component. -/
def ConState.pendingCount (s : ConState) : ℕ :=
  (Finset.univ.filter (fun k : Fin s.numDiv => s.cleared < s.divTilde k)).card

/-- **The state invariant** (rung 2; shape-locked, detail loose). The layer has not overshot the
chain (`S ≤ L`) and the cleared count has not overshot the within-layer ceiling (`J ≤ layerCap`).
These are the facts the descent lemmas' strict preconditions refine (a rollover needs `S ≤ L`; a
`J`-advancing step needs `J < layerCap`). -/
structure StateInvariant (M : Fin (L + 1) → ℕ) (s : ConState) : Prop where
  /-- The layer has not overshot the chain. -/
  layer_le : s.layer ≤ L
  /-- The cleared count has not overshot the within-layer ceiling. -/
  cleared_le : s.cleared ≤ layerCap M

/-! ## The lex-triple measure + well-founded relation (the pinned idiom) -/

/-- **The termination measure** `μ = lex(L+1−S, layerCap−J, pendingCount)` on `ℕ ×ₗ ℕ ×ₗ ℕ`
(well-founded — the banked `RouteMState` idiom). Component 1 drops at a layer rollover, component 2
at a `J`-advancing case-1(2)/case-2 step, component 3 at a case-1(1) merge. -/
def conMeasure (M : Fin (L + 1) → ℕ) (s : ConState) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (L + 1 - s.layer, toLex (layerCap M - s.cleared, s.pendingCount))

/-- The recursion's well-founded relation: strictly-smaller μ. -/
def conRel (M : Fin (L + 1) → ℕ) (s t : ConState) : Prop := conMeasure M s < conMeasure M t

/-- `conRel` is well-founded (pullback of `<` on the lex triple along `conMeasure`). Mirrors the
banked `routeRel_wf`; the lex-`<` is well-founded via the `WellFoundedLT (α ×ₗ β)` instance. -/
theorem conRel_wf (M : Fin (L + 1) → ℕ) : WellFounded (conRel M) :=
  InvImage.wf (conMeasure M) wellFounded_lt

/-! ## The per-case transitions + μ-descent (rung 2B)

Each of the construction's four step kinds is a `ConState → ConState` map, and each strictly drops a
μ component under its step precondition — so `conRel (step s) s` holds and the recursion is
well-founded. The KILL-CONDITION (a step decreasing NO component ⇒ design break) is CLEARED: every
transition below drops a component. `stepAppendAdvance` covers BOTH case-1(2) and case-2 (they
differ only in the appended exponent, which μ does not read) — both drop component 2. -/

/-- **case-1(1) merge transition**: divisor `i`'s clearing level drops to the cleared count
(`t̃_i → J`); the ledger is otherwise unchanged (the exponent bump `divExp_i += runLen·resCols` does
not affect μ, so the carrier records only the `t̃` drop). -/
def ConState.stepCase11 (s : ConState) (i : Fin s.numDiv) : ConState :=
  ⟨s.layer, s.cleared, s.numDiv, s.divExp, Function.update s.divTilde i s.cleared⟩

/-- **case-1(2)/case-2 transition**: append a new divisor of exponent `e` at clearing level `J`
(`t̃ = cleared`), then advance the cleared count by one. The two cases differ ONLY in the appended
exponent `e`, which μ does not read — both drop component 2. -/
def ConState.stepAppendAdvance (s : ConState) (e : ℕ) : ConState :=
  ⟨s.layer, s.cleared + 1, s.numDiv + 1, Fin.snoc s.divExp e, Fin.snoc s.divTilde s.cleared⟩

/-- **Layer rollover transition**: advance the layer (`S → S+1`) and reset the cleared count
(`J → 0`); the divisor ledger carries over. -/
def ConState.stepRollover (s : ConState) : ConState :=
  ⟨s.layer + 1, 0, s.numDiv, s.divExp, s.divTilde⟩

/-- A case-1(1) merge strictly drops the pending-divisor count: its target divisor `i` (pending,
`J < t̃_i`) has `t̃_i` reset to `J`, leaving the pending set with `i` erased. (In the construction
the precondition `J < t̃_i` is the eligibility conjunct `t̃_i = J + runLen` with `runLen ≥ 1`.) -/
theorem pendingCount_stepCase11_lt (s : ConState) (i : Fin s.numDiv)
    (hi : s.cleared < s.divTilde i) :
    (s.stepCase11 i).pendingCount < s.pendingCount := by
  have hset : (Finset.univ.filter
        (fun k : Fin s.numDiv => s.cleared < Function.update s.divTilde i s.cleared k))
      = (Finset.univ.filter (fun k : Fin s.numDiv => s.cleared < s.divTilde k)).erase i := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]; tauto
  have hmem : i ∈ Finset.univ.filter (fun k : Fin s.numDiv => s.cleared < s.divTilde k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  -- State the inequality with a single DecidablePred synthesis point (matching `hset`), then close
  -- the goal by defeq: `(s.stepCase11 i).pendingCount` reduces to this LHS through the projections.
  have hlt : (Finset.univ.filter
        (fun k : Fin s.numDiv => s.cleared < Function.update s.divTilde i s.cleared k)).card
      < (Finset.univ.filter (fun k : Fin s.numDiv => s.cleared < s.divTilde k)).card := by
    rw [hset]; exact Finset.card_erase_lt_of_mem hmem
  exact hlt

/-- **case-1(1) drops μ (component 3).** Given the eligible (pending) target, `conRel` holds — the
layer and cleared count are unchanged, so μ₁, μ₂ tie and μ₃ (`pendingCount`) drops. -/
theorem conRel_stepCase11 (M : Fin (L + 1) → ℕ) (s : ConState) (i : Fin s.numDiv)
    (hi : s.cleared < s.divTilde i) :
    conRel M (s.stepCase11 i) s := by
  unfold conRel conMeasure
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨rfl, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, pendingCount_stepCase11_lt s i hi⟩

/-- **case-1(2)/case-2 drops μ (component 2).** Advancing `J` by one strictly drops `layerCap − J`
(the precondition `J < layerCap` gives room); the layer ties, so μ₁ ties and μ₂ drops. -/
theorem conRel_stepAppendAdvance (M : Fin (L + 1) → ℕ) (s : ConState) (e : ℕ)
    (hlt : s.cleared < layerCap M) :
    conRel M (s.stepAppendAdvance e) s := by
  unfold conRel conMeasure
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨rfl, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inl ?_
  change layerCap M - (s.cleared + 1) < layerCap M - s.cleared
  omega

/-- **Layer rollover drops μ (component 1).** Advancing `S` by one strictly drops `L+1 − S` (the
precondition `S ≤ L` gives room); μ₁ drops, so μ₂/μ₃ may reset freely. -/
theorem conRel_stepRollover (M : Fin (L + 1) → ℕ) (s : ConState) (hlayer : s.layer ≤ L) :
    conRel M s.stepRollover s := by
  unfold conRel conMeasure
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inl ?_
  change L + 1 - (s.layer + 1) < L + 1 - s.layer
  omega

end DLNFibre.DLN.RLCT.Engine
