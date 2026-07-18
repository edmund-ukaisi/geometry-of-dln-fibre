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

The carrier is the FAITHFUL construction state (rung T1c): the layer `S`, the cleared-pivot count
`J`, and the exceptional-divisor ledger carrying the full rank-pattern vectors `T_{s,k}` (PRIMITIVE)
and the `genDivExp` sharing-multiplicity ledger, alongside the exponents `M_{s,k}`. The clearing
level `t̃_{s,k}` is DERIVED (`= min T_{s,k}`), as on the tree carrier. Derivable data
(`resRows`/`resCols`/`depth`/`minAdm`) is not stored — computed from `M`, `S`, `J`. (`runLen = J₁`
is NOT in this list — it is profile-determined, the gap to the next occupied `t̃` level.) Mirrors
the tree-node `StepData`; `ConState` threads `T` for the divisor-chooser (whose interface type lands
here) and drives the termination measure.

Per-case descent (rung 2B) lives below the measure: a case-1(1) merge drops component 3
(`pendingCount`); a case-1(2)/case-2 step drops component 2 (`J` advances by one); a layer rollover
drops component 1 (`S` advances). No case decreases NOTHING — the termination kill-condition.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ}

/-! ## The termination carrier + invariant -/

/-- **The construction's FAITHFUL termination carrier** (rung T1c): the double-induction state.
`layer` is `S`, `cleared` is `J`, `divExp` the exponents `M_{s,k}`, `divProfile` the full
rank-pattern vectors `T_{s,k}` (PRIMITIVE; `t̃` derived via `ConState.divTilde = tildeOf ∘
divProfile`), and `genDivExp` the generator-divisor sharing-multiplicity ledger (field-only at R1;
propagation at T4). -/
structure ConState (L : ℕ) where
  /-- The layer index `S`. -/
  layer : ℕ
  /-- The count `J` of unit pivots cleared in the current layer. -/
  cleared : ℕ
  /-- Number of exceptional divisors currently in scope. -/
  numDiv : ℕ
  /-- The per-divisor exponent ledger `M_{s,k}`. -/
  divExp : Fin numDiv → ℕ
  /-- **The per-divisor rank-pattern vector** `T_{s,k}` (full-T PRIMITIVE; `t̃` derived). -/
  divProfile : Fin numDiv → (Fin L → ℕ)
  /-- Number of residual generators tracked for sharing. -/
  numGen : ℕ
  /-- The generator-divisor multiplicity ledger (support = nonzero locus; propagation at T4). -/
  genDivExp : Fin numGen → Fin numDiv → ℕ

/-- Derived per-divisor clearing level `t̃_{s,k} = min T_{s,k}` (the same derivation as the tree
carrier's `StepData.divTilde`). -/
def ConState.divTilde {L : ℕ} (s : ConState L) (k : Fin s.numDiv) : ℕ :=
  tildeOf (s.divProfile k)

/-- The within-layer ceiling on `J` (`cleared`): the total width `∑ M`, a fixed upper bound on the
cleared count in any layer (`J ≤ M(S) ≤ ∑ M`, and `J` resets to `0` at a rollover). Used as μ's 2nd
lex component's ceiling so `layerCap − J` strictly drops when `J` advances. -/
def layerCap (M : Fin (L + 1) → ℕ) : ℕ := ∑ i, M i

/-- **The pending-divisor count**: divisors whose clearing level exceeds the current cleared count
(`t̃_k > J`). μ's third lex component. A case-1(1) merge moves its target divisor's `t̃` down to
`J`, so this drops by one; the other cases leave it dominated by a strict drop in a higher
component. -/
def ConState.pendingCount {L : ℕ} (s : ConState L) : ℕ :=
  (Finset.univ.filter (fun k : Fin s.numDiv => s.cleared < s.divTilde k)).card

/-- **The state invariant** (rung 2 → o1 strengthening).

**Indexing (pinned):** Lean `layer` is the 0-INDEXED paper layer, `layer = S − 1` (root `layer = 0`
is paper `S = 1`; forced by the T-rule `setTail` `layer ≤ p` giving the page's tail `t⁽ˢ⁾…⁽ᴸ⁾`, and
confirmed by the `(1,1)→(1,0)` `M=8` merge occurring at paper `S=2` = Lean `layer=1`).

The layer has not overshot the chain (`layer ≤ L`), the cleared count has not overshot the coarse
ceiling (`J ≤ layerCap`), and — the o1 `[add]`, **read off the simulator's rollover guard** — the
LIVE-LAYER width bound `live_width`: the cleared count never exceeds the running-min width THROUGH
the current layer, `J ≤ min(M i : i ≤ layer) = min(M⁽¹⁾…M⁽ˢ⁾) = Mrun(S)`. (The simulator advances
when `J ≥ MSp1 = min(Mrun(S), M⁽ˢ⁺¹⁾) ≤ Mrun(S)`, so `J < MSp1 ≤ Mrun(S)` gives this a fortiori;
numerically confirmed at all reachable states of `(2,2,2)`, `(3,3,4)`, `(2,2,2,2)`, `(2,2,3,2)`, and
the higher-`L` clarifier instances `(2,2,3,3,2)`, `(3,2,4,2)`.) `live_width` discharges the case-2
append's weak-decrease head-domination (head index `≤ layer−1`, so `cleared ≤ runMinWidth`) and
feeds the leaf block-bound. The COMPARABILITY component finalized as `SameLevelChainInv` (o4 cert:
the paper's full chain is refuted; same-t̃ comparability holds and is what o2 needs). -/
structure StateInvariant (M : Fin (L + 1) → ℕ) (s : ConState L) : Prop where
  /-- The layer has not overshot the chain. -/
  layer_le : s.layer ≤ L
  /-- The cleared count has not overshot the coarse within-layer ceiling. -/
  cleared_le : s.cleared ≤ layerCap M
  /-- **The live-layer width bound** (o1, simulator read-off): `J ≤ min(M i : i ≤ layer)` (the
  running-min width through the current layer, `= Mrun(S)` with `layer = S−1`), universal form. -/
  live_width : ∀ i : Fin (L + 1), (i : ℕ) ≤ s.layer → s.cleared ≤ M i

/-! ## The lex-triple measure + well-founded relation (the pinned idiom) -/

/-- **The termination measure** `μ = lex(L+1−S, layerCap−J, pendingCount)` on `ℕ ×ₗ ℕ ×ₗ ℕ`
(well-founded — the banked `RouteMState` idiom). Component 1 drops at a layer rollover, component 2
at a `J`-advancing case-1(2)/case-2 step, component 3 at a case-1(1) merge. -/
def conMeasure (M : Fin (L + 1) → ℕ) (s : ConState L) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (L + 1 - s.layer, toLex (layerCap M - s.cleared, s.pendingCount))

/-- The recursion's well-founded relation: strictly-smaller μ. -/
def conRel (M : Fin (L + 1) → ℕ) (s t : ConState L) : Prop := conMeasure M s < conMeasure M t

/-- `conRel` is well-founded (pullback of `<` on the lex triple along `conMeasure`). Mirrors the
banked `routeRel_wf`; the lex-`<` is well-founded via the `WellFoundedLT (α ×ₗ β)` instance. -/
theorem conRel_wf (M : Fin (L + 1) → ℕ) : WellFounded (conRel M) :=
  InvImage.wf (conMeasure M) wellFounded_lt

/-! ## The `T`-rule tail-write + its `tildeOf` bound (T1c) -/

/-- The `T`-rule tail-write (mirrors `stepUpdate`'s local `setTail`): the tail `t⁽ˢ⁾…⁽ᴸ⁾ := J`
(indices `layer ≤ p.val`), the head left as `T`. -/
def setTail {L : ℕ} (layer cleared : ℕ) (T : Fin L → ℕ) : Fin L → ℕ :=
  fun p => if layer ≤ (p : ℕ) then cleared else T p

/-- `tildeOf T = min T ≤ T i` for any coordinate `i` (the min is `≤` every entry). -/
theorem tildeOf_le {L : ℕ} {T : Fin L → ℕ} (i : Fin L) : tildeOf T ≤ T i := by
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  haveI : Nonempty (Fin L) := ⟨i⟩
  simp only [tildeOf, dif_pos hL]
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- **The clearing level drops to `J` after a tail-write** (the case-1(1) merge fact): if there is a
tail coordinate (`layer < L`), then `t̃ = min (setTail layer J T) ≤ J` — the tail index `L−1`
carries value `J`. The load-bearing bound of the reworked `pendingCount` descent. -/
theorem tildeOf_setTail_le {L : ℕ} {layer cleared : ℕ} {T : Fin L → ℕ} (h : layer < L) :
    tildeOf (setTail layer cleared T) ≤ cleared := by
  have hle : layer ≤ (⟨L - 1, by omega⟩ : Fin L).val := by change layer ≤ L - 1; omega
  have hval : setTail layer cleared T ⟨L - 1, by omega⟩ = cleared := by
    simp only [setTail]; rw [if_pos hle]
  exact le_of_le_of_eq (tildeOf_le ⟨L - 1, by omega⟩) hval

/-- **A tail-write preserves weak-decrease** given the head is weak-decreasing and dominates the
written tail value `cleared`: `setTail layer cleared T` is antitone. The head (`p < layer`) keeps
`T` (weak-dec by `hwd`); the tail (`p ≥ layer`) is the constant `cleared`, `≤` the head by `hc`. The
common engine of the case-1(1) and case-2 weak-decrease preservation. -/
theorem setTail_antitone {L : ℕ} {layer cleared : ℕ} {T : Fin L → ℕ}
    (hwd : ∀ i j : Fin L, i ≤ j → T j ≤ T i)
    (hc : ∀ p : Fin L, (p : ℕ) < layer → cleared ≤ T p)
    {a b : Fin L} (hab : a ≤ b) :
    setTail layer cleared T b ≤ setTail layer cleared T a := by
  have hab' : (a : ℕ) ≤ (b : ℕ) := hab
  simp only [setTail]
  split_ifs with hb ha
  · exact le_refl _
  · exact hc a (by omega)
  · omega
  · exact hwd a b hab

/-! ## The per-case transitions + μ-descent (rung 2B)

Each of the construction's four step kinds is a `ConState → ConState` map, and each strictly drops a
μ component under its step precondition — so `conRel (step s) s` holds and the recursion is
well-founded. The KILL-CONDITION (a step decreasing NO component ⇒ design break) is CLEARED: every
transition below drops a component. `stepAppendAdvance` covers BOTH case-1(2) and case-2 (they
differ only in the appended exponent, which μ does not read) — both drop component 2. -/

/-- **case-1(1) merge transition**: mutate divisor `i`'s rank-pattern via the `T`-rule tail-write
(`setTail`), so its derived clearing level drops to `J`; the ledger is otherwise unchanged (the
exponent bump does not affect μ). -/
def ConState.stepCase11 {L : ℕ} (s : ConState L) (i : Fin s.numDiv) : ConState L :=
  ⟨s.layer, s.cleared, s.numDiv, s.divExp,
    Function.update s.divProfile i (setTail s.layer s.cleared (s.divProfile i)),
    s.numGen, s.genDivExp⟩

/-- **case-1(2)/case-2 transition**: append a new divisor of exponent `e` and (tail-written)
rank-pattern `t₀`, then advance the cleared count by one. The two cases differ ONLY in `e`/`t₀`,
which μ does not read — both drop component 2. The new divisor's `genDivExp` column is `0`
(placeholder; real sharing propagation is T4). -/
def ConState.stepAppendAdvance {L : ℕ} (s : ConState L) (e : ℕ) (t₀ : Fin L → ℕ) : ConState L :=
  ⟨s.layer, s.cleared + 1, s.numDiv + 1, Fin.snoc s.divExp e,
    Fin.snoc s.divProfile (setTail s.layer s.cleared t₀),
    s.numGen, fun g => Fin.snoc (s.genDivExp g) 0⟩

/-- **Layer rollover transition**: advance the layer (`S → S+1`) and reset the cleared count
(`J → 0`); the divisor ledger carries over. -/
def ConState.stepRollover {L : ℕ} (s : ConState L) : ConState L :=
  ⟨s.layer + 1, 0, s.numDiv, s.divExp, s.divProfile, s.numGen, s.genDivExp⟩

/-- A case-1(1) merge strictly drops the pending-divisor count: its target divisor `i` (pending,
`J < t̃_i`) has its rank-pattern tail-written, so the derived `t̃_i` drops to `≤ J` (needs a tail
coordinate, `layer < L`), leaving the pending set with `i` erased. (In the construction the
precondition `J < t̃_i` is the eligibility conjunct `t̃_i = J + runLen`, `runLen ≥ 1`.) -/
theorem pendingCount_stepCase11_lt {L : ℕ} (s : ConState L) (i : Fin s.numDiv)
    (hlayer : s.layer < L) (hi : s.cleared < s.divTilde i) :
    (s.stepCase11 i).pendingCount < s.pendingCount := by
  set upd := Function.update s.divProfile i (setTail s.layer s.cleared (s.divProfile i)) with hupd
  have hnp : tildeOf (upd i) ≤ s.cleared := by
    rw [hupd, Function.update_self]; exact tildeOf_setTail_le hlayer
  have hset : (Finset.univ.filter (fun k : Fin s.numDiv => s.cleared < tildeOf (upd k)))
      = (Finset.univ.filter (fun k : Fin s.numDiv => s.cleared < tildeOf (s.divProfile k))).erase i
      := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hk : k = i
    · subst hk
      simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_lt]
      exact hnp
    · rw [hupd, Function.update_of_ne hk]; tauto
  have hmem : i ∈ Finset.univ.filter
      (fun k : Fin s.numDiv => s.cleared < tildeOf (s.divProfile k)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  -- One DecidablePred synthesis point (matching `hset`); the goal reduces to this LHS by defeq
  -- (`(stepCase11).divTilde k = tildeOf ((stepCase11).divProfile k)`, `divProfile = upd`).
  have hlt : (Finset.univ.filter (fun k : Fin s.numDiv => s.cleared < tildeOf (upd k))).card
      < (Finset.univ.filter
          (fun k : Fin s.numDiv => s.cleared < tildeOf (s.divProfile k))).card := by
    rw [hset]; exact Finset.card_erase_lt_of_mem hmem
  exact hlt

/-- **case-1(1) drops μ (component 3).** Given the eligible (pending) target, `conRel` holds — the
layer and cleared count are unchanged, so μ₁, μ₂ tie and μ₃ (`pendingCount`) drops. -/
theorem conRel_stepCase11 (M : Fin (L + 1) → ℕ) (s : ConState L) (i : Fin s.numDiv)
    (hlayer : s.layer < L) (hi : s.cleared < s.divTilde i) :
    conRel M (s.stepCase11 i) s := by
  unfold conRel conMeasure
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨rfl, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, pendingCount_stepCase11_lt s i hlayer hi⟩

/-- **case-1(2)/case-2 drops μ (component 2).** Advancing `J` by one strictly drops `layerCap − J`
(the precondition `J < layerCap` gives room); the layer ties, so μ₁ ties and μ₂ drops. -/
theorem conRel_stepAppendAdvance (M : Fin (L + 1) → ℕ) (s : ConState L) (e : ℕ) (t₀ : Fin L → ℕ)
    (hlt : s.cleared < layerCap M) :
    conRel M (s.stepAppendAdvance e t₀) s := by
  unfold conRel conMeasure
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨rfl, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inl ?_
  change layerCap M - (s.cleared + 1) < layerCap M - s.cleared
  omega

/-- **Layer rollover drops μ (component 1).** Advancing `S` by one strictly drops `L+1 − S` (the
precondition `S ≤ L` gives room); μ₁ drops, so μ₂/μ₃ may reset freely. -/
theorem conRel_stepRollover (M : Fin (L + 1) → ℕ) (s : ConState L) (hlayer : s.layer ≤ L) :
    conRel M s.stepRollover s := by
  unfold conRel conMeasure
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inl ?_
  change L + 1 - (s.layer + 1) < L + 1 - s.layer
  omega

/-! ## The divisor-chooser interface (T1c; TYPE only, proofs at T4) -/

/-- **The divisor-chooser SPEC** (rung R1 TYPE; the chooser's PROOFS are T4). At a case-1 step the
construction must SELECT which divisor `k` to blow up: it must have a POSITIVE run (`1 ≤ runLen`,
the gap condition — `runLen = J₁ ≥ 1` is the run to the next occupied `t̃` level, Aoyagi p.15), be
at clearing level `t̃_k = J + J₁` (ELIGIBILITY), and be Def-4-MINIMAL among all eligible divisors —
its full rank-pattern `T_k` is componentwise `≤ T_{k'}` for every `k'` (Def. 4, p.14). The
`1 ≤ runLen` conjunct is the gap condition's cheapest faithful shadow; it also feeds the case-1(1)
μ-descent (with `runLen ≥ 1` the eligible divisor is genuinely pending, `t̃_k > J`). This is why the
carrier is full-`T`, not `t̃`-only: `cert-atlas-probe-2222` verdict (c) proved the MINIMALITY is
load-bearing for COMPARABILITY-PRESERVATION, NOT value-protection — at `(2,2,2,2)` node
`(S,J,J₁)=(3,0,1)` the WRONG pick yields `(2,1,0)`, INCOMPARABLE with the right `(1,1,1)` (breaking
the total-comparability invariant principalization rides on, p.15), even though `minAdm` is `3`
under BOTH picks. A finiteness-only certificate is provably blind to a wrong tie-break; only the
full-`T` chooser sees it. (The kill-witness — the chooser rejects `(2,1,1)` there — is a T4
`¬`-witness.) -/
def IsEligibleMinimalChoice {L : ℕ} (s : ConState L) (k : Fin s.numDiv) (runLen : ℕ) : Prop :=
  1 ≤ runLen ∧
    s.divTilde k = s.cleared + runLen ∧
      ∀ k' : Fin s.numDiv, s.divTilde k' = s.cleared + runLen →
        ∀ j : Fin L, s.divProfile k j ≤ s.divProfile k' j

/-! ## T2: the recursion-assembly WF-fix pin

Before the full tree-assembly, pin the recursion machinery: `WellFounded.fix (conRel_wf M)` supports
a construction recursion on `ConState L` whose recursive call lands on any `conRel`-smaller child
(the output of a step, its descent supplied by the `conRel_step*` lemmas). This mirrors the μ-lex
pin (rung 2A): fix the syntax at the v4.29 pin, then build the real `buildTree` (producing the
`ResolutionTree` + discharging the ledger/StepRel/base/exponent/live conjuncts of
`CanonicalResolution`, with the chart-producer and `ChartBridge` as the T3 typed holes) on top. -/

/-- **The step oracle** (T2): at a state `s`, the construction either TERMINATES (`none`, → a leaf)
or takes a step to a `conRel`-SMALLER child (`some ⟨s', h⟩`, the descent `h` from a `conRel_step*`
lemma). The real construction instantiates this from the divisor-chooser + the case dispatch; the
skeleton is generic over it. -/
abbrev StepOracle (M : Fin (L + 1) → ℕ) :=
  (s : ConState L) → Option {s' : ConState L // conRel M s' s}

/-- **Recursion-syntax pin** (T2): `WellFounded.fix (conRel_wf M)` elaborates with the recursive
call on the `conRel`-smaller child. `conStepDepth` counts steps down the oracle's chain — a generic
body confirming the WF machinery before the tree-valued `buildTree`. -/
noncomputable def conStepDepth (M : Fin (L + 1) → ℕ) (oracle : StepOracle M) : ConState L → ℕ :=
  WellFounded.fix (conRel_wf M) fun s rec =>
    match oracle s with
    | none => 0
    | some ⟨s', h⟩ => rec s' h + 1

/-! ## T2: the tree-valued construction recursion (`buildTree`)

The real construction: a `ConState L`-indexed decision (`ConDecision`) at each state either
TERMINATES (a `LeafData`) or STEPS to a NODE (`StepData`) with a `List` of `conRel`-smaller child
states, and `buildTree = WellFounded.fix (conRel_wf M)` folds it into a concrete `ResolutionTree M`.
This is the recursion ASSEMBLY (task T2): it produces the tree; the CanonicalResolution conjuncts
are discharged on top of it by structural induction (StepRel/base — from the decision's
per-edge/root guarantees) and by the deep termination content (IsFullMonomialization / exponent
hooks — GATED, with the ChartBridge/`srcBox` the T3 holes).

The decision carries the two ledger-consistency guarantees the downstream discharge consumes: the
emitted node/leaf's ledger EQUALS the state's (`hnode`/`hleaf`, design §1/§2 `hledger`), so the
per-state lemma `rootLedger_buildTree` below reads the child ledger off the child state — the
load-bearing bridge for the rfl-class `StepRel` equality (a child born of the
`stepUpdate`-transitioned state has `rootLedger = stepUpdate`). -/

/-- The `RootLedger` a `ConState` presents (its exponent/clearing core) — the shape a step's child
must match for the rfl-class `StepRel` equality. -/
def ConState.toRootLedger {L : ℕ} (s : ConState L) : ResolutionTree.RootLedger L :=
  ⟨s.numDiv, s.divExp, s.divProfile, s.cleared⟩

/-- **One `conRel`-smaller child of a step** at state `s`: its edge `case`/`subst`, the child state
`child` the recursion descends into, and the descent proof `hdesc : conRel M child s` (from the
`conRel_step*` descent lemmas). `buildTree` turns it into `Edge.mk case subst (buildTree child)`. -/
structure StepChild (M : Fin (L + 1) → ℕ) (s : ConState L) where
  /-- The edge's case tag. -/
  ecase : StepCase
  /-- The edge's substitution ledger. -/
  esubst : ChartSubst M
  /-- The `conRel`-smaller child state (the `stepUpdate`-transitioned state). -/
  child : ConState L
  /-- The descent proof — the recursion may recurse on `child`. -/
  hdesc : conRel M child s

/-- **The per-state construction decision** (T2, design §1). At `s` the construction either
TERMINATES into a `LeafData` (whose full-ledger core matches `s`) or STEPS to a `StepData` node
(whose ledger core matches `s`) with a `List` of `conRel`-smaller children. The `hleaf`/`hnode`
ledger-match guarantees are what `rootLedger_buildTree` folds into the per-state ledger identity. -/
inductive ConDecision (M : Fin (L + 1) → ℕ) (s : ConState L) where
  /-- Terminate: emit a leaf whose FULL-ledger core equals `s`'s. -/
  | terminal (l : LeafData M)
      (hleaf : ResolutionTree.rootLedger (ResolutionTree.leaf l) = s.toRootLedger) :
      ConDecision M s
  /-- Step: emit a node with `conRel`-smaller children. The guarantees (design §1 `StepEmit`):
  `hnode` — the node's ledger core equals `s`'s (`rootLedger` on a `branch` ignores the edges, so it
  is stated on the core directly); `hlayer` — the node's layer equals `s`'s (the `RootLedger` core
  drops `layer`, so `base` needs this separately); `hstep` — each child is the
  `stepUpdate`-transitioned state (ledger core `= stepUpdate node case subst`) AND, for a
  case-1(1)/1(2) edge, the merge target is eligible. `hstep` is exactly the per-edge `StepRel`
  content, phrased on the child STATE (bridged to the child SUBTREE by `rootLedger_buildTree`). -/
  | step (node : StepData M) (children : List (StepChild M s))
      (hnode : (⟨node.numDiv, node.divExp, node.divProfile, node.cleared⟩ :
          ResolutionTree.RootLedger L) = s.toRootLedger)
      (hlayer : node.layer = s.layer)
      (hstep : ∀ c ∈ children,
        c.child.toRootLedger = stepUpdate node c.ecase c.esubst ∧
          ((c.ecase = StepCase.case11 ∨ c.ecase = StepCase.case12) →
            ∃ h : c.esubst.mergeIdx < node.numDiv,
              node.divTilde ⟨c.esubst.mergeIdx, h⟩ = node.cleared + c.esubst.runLen)) :
      ConDecision M s

/-- **The tree-valued construction recursion** (T2): `WellFounded.fix (conRel_wf M)` folds the
per-state `oracle` decision into a concrete `ResolutionTree M`. A terminal decision emits its leaf;
a step decision emits its node with one `Edge` per child, the child subtree from the recursive call
on the `conRel`-smaller child state (descent from `StepChild.hdesc`). -/
noncomputable def buildTree (M : Fin (L + 1) → ℕ)
    (oracle : (s : ConState L) → ConDecision M s) : ConState L → ResolutionTree M :=
  WellFounded.fix (conRel_wf M) fun s rec =>
    match oracle s with
    | .terminal l _ => ResolutionTree.leaf l
    | .step node children _ _ _ =>
        ResolutionTree.branch node
          (children.map (fun c => Edge.mk c.ecase c.esubst (rec c.child c.hdesc)))

/-- **The per-state ledger identity** (T2, the StepRel bridge): the root ledger of `buildTree … s`
equals the ledger `s` presents. A terminal leaf's ledger is `hleaf`; a step node's ledger reads its
`StepData` core, which — since `rootLedger` on a `branch` ignores the edges — equals the state's by
`hnode`. This is what makes the child of a `stepUpdate`-transitioned state satisfy the rfl-class
`StepRel` equality (discharged over the whole tree in the next unit). -/
theorem rootLedger_buildTree (M : Fin (L + 1) → ℕ)
    (oracle : (s : ConState L) → ConDecision M s) (s : ConState L) :
    ResolutionTree.rootLedger (buildTree M oracle s) = s.toRootLedger := by
  rw [buildTree, WellFounded.fix_eq]
  -- `rootLedger (branch node _)` reads the node core, ignoring the edge list; a leaf's is `hleaf`.
  cases h : oracle s with
  | terminal l hleaf => exact hleaf
  | step node children hnode hlayer hstep => exact hnode

/-- **`buildTree` unfolding at a terminal decision**: the tree is the emitted leaf. -/
theorem buildTree_terminal (M : Fin (L + 1) → ℕ)
    (oracle : (s : ConState L) → ConDecision M s) (s : ConState L) (l : LeafData M)
    (hleaf : ResolutionTree.rootLedger (ResolutionTree.leaf l) = s.toRootLedger)
    (hos : oracle s = ConDecision.terminal l hleaf) :
    buildTree M oracle s = ResolutionTree.leaf l := by
  rw [buildTree, WellFounded.fix_eq, hos]

/-- **`buildTree` unfolding at a step decision**: a `branch` whose edges recurse into the children,
each child subtree `buildTree … c.child`. The clean interface for `base` / `StepRel`. -/
theorem buildTree_step (M : Fin (L + 1) → ℕ)
    (oracle : (s : ConState L) → ConDecision M s) (s : ConState L) (node : StepData M)
    (children : List (StepChild M s)) {hnode hlayer hstep}
    (hos : oracle s = ConDecision.step node children hnode hlayer hstep) :
    buildTree M oracle s = ResolutionTree.branch node
      (children.map (fun c => Edge.mk c.ecase c.esubst (buildTree M oracle c.child))) := by
  conv_lhs => rw [buildTree, WellFounded.fix_eq]
  rw [hos]
  rfl

/-- **The base conjunct** (T2, `CanonicalResolution` §3): if the ROOT state (`layer = 0`,
`cleared = 0`) STEPS, `buildTree … s` is a `branch` whose node has `layer = 0` and `cleared = 0` —
the regular peel begins at `S = J = 0`. The node's `cleared` comes from `hnode` (ledger core matches
the state) and its `layer` from `hlayer` (the `RootLedger` core drops `layer`). -/
theorem base_of_buildTree (M : Fin (L + 1) → ℕ)
    (oracle : (s : ConState L) → ConDecision M s) (s : ConState L)
    (hs0 : s.layer = 0) (hsc : s.cleared = 0)
    (hstep : ∃ node children hnode hlayer hstepg,
        oracle s = ConDecision.step node children hnode hlayer hstepg) :
    ∃ (n : StepData M) (edges : List (Edge M)),
      buildTree M oracle s = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0 := by
  obtain ⟨node, children, hnode, hlayer, _, hos⟩ := hstep
  refine ⟨node, _, buildTree_step M oracle s node children hos, ?_, ?_⟩
  · rw [hlayer, hs0]
  · have hc : node.cleared = s.cleared := congrArg ResolutionTree.RootLedger.cleared hnode
    rw [hc, hsc]

/-- The step-edges reachable through a list of edges are the per-child step-edges concatenated
(`edgesStepEdges` unrolled to a `flatMap` over the children's subtrees) — the bridge from the mutual
`stepEdges`/`edgesStepEdges` recursion to a `List.mem_flatMap` argument. -/
theorem edgesStepEdges_eq {M : Fin (L + 1) → ℕ} (es : List (Edge M)) :
    ResolutionTree.edgesStepEdges es = es.flatMap (fun e => ResolutionTree.stepEdges e.child) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | mk c σ ch => rw [ResolutionTree.edgesStepEdges, ih, List.flatMap_cons]; rfl

/-- **StepRel on every parent–edge pair** (T2, `CanonicalResolution` §2): every edge of a
`buildTree`-produced tree satisfies the faithful `StepRel`. The ledger conjunct is the child's
`rootLedger` (`= c.child.toRootLedger` by `rootLedger_buildTree`, `= stepUpdate node …` by the
decision's `hstep`); the eligibility conjunct is `hstep` too. Proven by well-founded induction on
the state: a step node's edges split into its own children (discharged by `hstep`) and the deeper
step-edges (discharged by the IH on each `conRel`-smaller child). -/
theorem stepRel_all_of_buildTree (M : Fin (L + 1) → ℕ)
    (oracle : (s : ConState L) → ConDecision M s) (s : ConState L) :
    ∀ p ∈ ResolutionTree.stepEdges (buildTree M oracle s), StepRel p.1 p.2 := by
  refine (conRel_wf M).induction
    (C := fun s => ∀ p ∈ ResolutionTree.stepEdges (buildTree M oracle s), StepRel p.1 p.2) s ?_
  intro s ih
  cases h : oracle s with
  | terminal l hleaf =>
      rw [buildTree_terminal M oracle s l hleaf h]
      intro p hp
      simp only [ResolutionTree.stepEdges, List.not_mem_nil] at hp
  | step node children hnode hlayer hstep =>
      rw [buildTree_step M oracle s node children h]
      intro p hp
      rw [ResolutionTree.stepEdges, List.mem_append] at hp
      rcases hp with hp1 | hp2
      · -- p is one of this node's own edges
        rw [List.mem_map] at hp1
        obtain ⟨e, he, rfl⟩ := hp1
        rw [List.mem_map] at he
        obtain ⟨c, hc, rfl⟩ := he
        obtain ⟨hled, helig⟩ := hstep c hc
        refine ⟨?_, ?_⟩
        · change ResolutionTree.rootLedger (buildTree M oracle c.child)
              = stepUpdate node c.ecase c.esubst
          rw [rootLedger_buildTree]; exact hled
        · exact helig
      · -- p is a deeper step-edge — recurse via the IH on the child state
        rw [edgesStepEdges_eq, List.mem_flatMap] at hp2
        obtain ⟨e, he, hpe⟩ := hp2
        rw [List.mem_map] at he
        obtain ⟨c, hc, rfl⟩ := he
        exact ih c.child c.hdesc p hpe

/-! ## T2 build-side invariants (TYPES only; preservation proofs are buildTree bricks) -/

/-- **The per-node profile bundle** (elder-gate4 §3a): WEAK-DECREASE + BLOCK-BOUND. **CORRECTED
(finding, `stepUpdate_preserves_weakInv` scope):** only WEAK-DECREASE (`WeakDecInv` below) is
per-node preservable; the BLOCK-BOUND conjunct (`t⁽ʲ⁾ ≤ admBound M j`) is a LEAF property, NOT
per-node — a case-1(1)/case-2 tail-write sets the tail to `cleared = J`, and at a narrow later layer
`J > admBound M p` (e.g. `M=(2,3,3,1)`: a Case-2 tail-write gives `t⁽³⁾=2 > admBound=M⁽³⁾=1`), so
block-bound is recovered only at a leaf where `J = 0` (tail `= 0 ≤ admBound`), exactly like the
last-component-zero property. Neither this nor `∈ Adm` is a per-node invariant (a PENDING node has
`t̃ = min T > 0`, last component `> 0`, so `∉ Adm` clause 3). `∈ Adm` is the LEAF property
`WeakDecInv + block-bound(leaf) + leaf-t̃=0` (post-final-rollover `J=0`). The bundle is retained as
the LEAF target; the per-node brick is `WeakDecInv_step*` below (the pnp (2,2,3,2) verdict confirms
FIX-A's running-min reset restores weak-decrease, where raw-`T` broke it). -/
def WeakProfileInv (M : Fin (L + 1) → ℕ) (s : ConState L) : Prop :=
  ∀ k : Fin s.numDiv,
    (∀ i j : Fin L, i ≤ j → s.divProfile k j ≤ s.divProfile k i) ∧
      (∀ j : Fin L, s.divProfile k j ≤ admBound M j)

/-- **The sound per-node weak-decrease invariant**: each divisor's rank-pattern is weak-decreasing
(`i ≤ j → T_j ≤ T_i`) — `WeakProfileInv`'s first conjunct, and (per the finding above) the only
per-node-preservable part. `WeakDecInv_step*` prove the three `ConState` transitions preserve it. -/
def WeakDecInv {L : ℕ} (s : ConState L) : Prop :=
  ∀ (k : Fin s.numDiv) (i j : Fin L), i ≤ j → s.divProfile k j ≤ s.divProfile k i

/-- **Layer rollover preserves weak-decrease** — the divisor ledger carries over unchanged. -/
theorem WeakDecInv_stepRollover {L : ℕ} (s : ConState L) (h : WeakDecInv s) :
    WeakDecInv s.stepRollover :=
  fun k i j hij => h k i j hij

/-- **A case-1(1) merge preserves weak-decrease.** The tail-written target `i` stays weak-decreasing
(`setTail_antitone`: its head is weak-dec by `h`, and dominates the written `cleared` since the
pending target has `cleared < t̃_i = min T_i ≤ T_i p`); the other divisors are unchanged. -/
theorem WeakDecInv_stepCase11 {L : ℕ} (s : ConState L) (i : Fin s.numDiv)
    (hi : s.cleared < s.divTilde i) (h : WeakDecInv s) : WeakDecInv (s.stepCase11 i) := by
  intro k a b hab
  simp only [ConState.stepCase11, Function.update_apply]
  split_ifs with hk
  · exact setTail_antitone (fun p q hpq => h i p q hpq)
      (fun p _ => le_of_lt (lt_of_lt_of_le hi (tildeOf_le p))) hab
  · exact h k a b hab

/-- **A case-1(2)/case-2 append preserves weak-decrease**, GIVEN the appended (pre-tail-write)
profile `t₀` is itself weak-decreasing and dominates `cleared` on the head (the concrete case-2
`runMinWidth` head and case-1(2) inherited head both satisfy this — the oracle supplies it). The old
divisors carry over (`Fin.snoc` at `castSucc`); the new one is `setTail … t₀` via
`setTail_antitone`. -/
theorem WeakDecInv_stepAppendAdvance {L : ℕ} (s : ConState L) (e : ℕ) (t₀ : Fin L → ℕ)
    (ht0wd : ∀ i j : Fin L, i ≤ j → t₀ j ≤ t₀ i)
    (ht0c : ∀ p : Fin L, (p : ℕ) < s.layer → s.cleared ≤ t₀ p)
    (h : WeakDecInv s) : WeakDecInv (s.stepAppendAdvance e t₀) := by
  intro k
  refine Fin.lastCases ?_ ?_ k
  · intro a b hab
    simp only [ConState.stepAppendAdvance, Fin.snoc_last]
    exact setTail_antitone ht0wd ht0c hab
  · intro k' a b hab
    simp only [ConState.stepAppendAdvance, Fin.snoc_castSucc]
    exact h k' a b hab

/-! ## o1: `StateInvariant` preservation (settled fields — `CompChainInv` held for the o4 join)

The strengthened `StateInvariant` (layer/coarse-cleared/live-width) is maintained by the three
transitions. A rollover STAYS LIVE (`layer < L`) — the final rollover (`layer = L`) exits into a
terminal state, which needs no invariant. The `J`-advancing append needs the STRICT live-width
(step-eligibility `J < min widths`, the simulator's `J < MSp1` guard) that the oracle supplies. -/

/-- **Layer rollover preserves `StateInvariant`** while staying live (`layer < L`): the new layer is
`≤ L`, the cleared count resets to `0` (`≤` everything). -/
theorem StateInvariant_stepRollover {L : ℕ} {M : Fin (L + 1) → ℕ} (s : ConState L)
    (hlayer : s.layer < L) (_h : StateInvariant M s) : StateInvariant M s.stepRollover := by
  refine ⟨?_, ?_, ?_⟩
  · change s.layer + 1 ≤ L; omega
  · change (0 : ℕ) ≤ layerCap M; exact Nat.zero_le _
  · intro i _; change (0 : ℕ) ≤ M i; exact Nat.zero_le _

/-- **A case-1(1) merge preserves `StateInvariant`** — it changes only a divisor profile, not the
layer or cleared count `StateInvariant` reads. -/
theorem StateInvariant_stepCase11 {L : ℕ} {M : Fin (L + 1) → ℕ} (s : ConState L) (i : Fin s.numDiv)
    (h : StateInvariant M s) : StateInvariant M (s.stepCase11 i) :=
  ⟨h.layer_le, h.cleared_le, h.live_width⟩

/-- **A case-1(2)/case-2 append preserves `StateInvariant`**, given the coarse room
(`cleared < layerCap`) and the STRICT live-width eligibility (`cleared < M i` for `i ≤ layer` — the
`J < MSp1` guard). The layer is unchanged; the cleared count advances by one and stays within both
bounds. -/
theorem StateInvariant_stepAppendAdvance {L : ℕ} {M : Fin (L + 1) → ℕ} (s : ConState L) (e : ℕ)
    (t₀ : Fin L → ℕ) (hcap : s.cleared < layerCap M)
    (helig : ∀ i : Fin (L + 1), (i : ℕ) ≤ s.layer → s.cleared < M i)
    (h : StateInvariant M s) : StateInvariant M (s.stepAppendAdvance e t₀) := by
  refine ⟨h.layer_le, ?_, ?_⟩
  · change s.cleared + 1 ≤ layerCap M; omega
  · intro i hi; change s.cleared + 1 ≤ M i; have := helig i hi; omega

/-- **The same-level comparability invariant** (o4-cert finalization of the held CompChainInv).
Divisors at a COMMON clearing level `t̃` are pairwise Def-4-comparable (componentwise `≤`).

**Why not the full chain:** the paper's p.15 TOTAL comparability (all pairs) is REFUTED
(`cert-compchain-o4.md` Part 1; minimal witness `M=(2,2,1,1)`: at an interior width-bottleneck a
Case-2 append `(2,1,0)` is incomparable with a stranded `(1,1,1)`). Scope: full-chain fails iff an
interior layer's running-min drops below `min(M⁽¹⁾,M⁽²⁾)` — a common DLN config. `HeadChainInv`
(global head-chain) is ALSO too strong (fails at `(3,3,1,1)`). `SameLevelChainInv` holds at every
reachable state (0/18 instances) and is EXACTLY what o2 needs: the eligible set `{t̃ = ℓ}` is
same-level, so a chain, so a Def-4 minimum EXISTS (`ChooserTotalOnChain`). Its preservation (o4
Lemmas A/B) consumes `SameLevelChainInv` + `FlatTail` (+ `WidthBound` for case-2) — NOT minimality
(both min/max picks preserve it). T3's principalization consumes level-filtration +
`SameLevelChainInv`, not full-chain (`cert-compchain-o4.md` Part 5(2)). -/
def SameLevelChainInv {L : ℕ} (s : ConState L) : Prop :=
  ∀ k k' : Fin s.numDiv, s.divTilde k = s.divTilde k' →
    (∀ j : Fin L, s.divProfile k j ≤ s.divProfile k' j) ∨
      (∀ j : Fin L, s.divProfile k' j ≤ s.divProfile k j)

/-- A tail coordinate (`layer ≤ p`) of a `setTail` is the written constant `cleared`. -/
theorem setTail_of_le {L : ℕ} {layer cleared : ℕ} {T : Fin L → ℕ} {p : Fin L}
    (h : layer ≤ (p : ℕ)) : setTail layer cleared T p = cleared := by
  simp only [setTail, if_pos h]

/-- **Flat tail** (o4-cert Part 3, the auxiliary invariant Lemmas A/B consume): every divisor's
tail — coords at index `≥ layer` (the page tail `t⁽ˢ⁾…⁽ᴸ⁾`, `layer = S−1`) — is CONSTANT. With
weak-decrease this pins `t̃ = the tail value`. Maintained: a tail-write (`setTail`) sets the tail to
the constant `cleared`; a rollover shrinks a constant suffix to a constant suffix. -/
def FlatTail {L : ℕ} (s : ConState L) : Prop :=
  ∀ (k : Fin s.numDiv) (i i' : Fin L), s.layer ≤ (i : ℕ) → s.layer ≤ (i' : ℕ) →
    s.divProfile k i = s.divProfile k i'

/-- **WidthBound** (o4-cert Part 3, consumed by the case-2 Lemma B): each divisor's HEAD (coords at
index `< layer`) is bounded by the running-min width `runMinWidth` (the Case-2 append head IS
`runMinWidth`; merges/appends keep the head `≤` it). -/
def WidthBound {L : ℕ} (M : Fin (L + 1) → ℕ) (s : ConState L) : Prop :=
  ∀ (k : Fin s.numDiv) (p : Fin L), (p : ℕ) < s.layer → s.divProfile k p ≤ runMinWidth M p

/-- **Layer rollover preserves `FlatTail`** — profiles carry over; a constant suffix (`≥ layer`)
restricts to a constant suffix (`≥ layer+1`). -/
theorem FlatTail_stepRollover {L : ℕ} (s : ConState L) (h : FlatTail s) :
    FlatTail s.stepRollover := by
  intro k i i' hi hi'
  have hi2 : s.layer ≤ (i : ℕ) := by change s.layer + 1 ≤ (i : ℕ) at hi; omega
  have hi2' : s.layer ≤ (i' : ℕ) := by change s.layer + 1 ≤ (i' : ℕ) at hi'; omega
  exact h k i i' hi2 hi2'

/-- **A case-1(1) merge preserves `FlatTail`** — the tail-written divisor has constant tail
`cleared`; the others are unchanged. -/
theorem FlatTail_stepCase11 {L : ℕ} (s : ConState L) (i : Fin s.numDiv) (h : FlatTail s) :
    FlatTail (s.stepCase11 i) := by
  intro k a a' ha ha'
  have ha2 : s.layer ≤ (a : ℕ) := ha
  have ha2' : s.layer ≤ (a' : ℕ) := ha'
  simp only [ConState.stepCase11, Function.update_apply]
  split_ifs with hk
  · rw [setTail_of_le ha2, setTail_of_le ha2']
  · exact h k a a' ha2 ha2'

/-- **A case-1(2)/case-2 append preserves `FlatTail`** — the appended `setTail … t₀` has constant
tail `cleared`; the old divisors are unchanged. -/
theorem FlatTail_stepAppendAdvance {L : ℕ} (s : ConState L) (e : ℕ) (t₀ : Fin L → ℕ)
    (h : FlatTail s) : FlatTail (s.stepAppendAdvance e t₀) := by
  intro k a a' ha ha'
  have ha2 : s.layer ≤ (a : ℕ) := ha
  have ha2' : s.layer ≤ (a' : ℕ) := ha'
  refine Fin.lastCases ?_ ?_ k
  · simp only [ConState.stepAppendAdvance, Fin.snoc_last]
    rw [setTail_of_le ha2, setTail_of_le ha2']
  · intro k'
    simp only [ConState.stepAppendAdvance, Fin.snoc_castSucc]
    exact h k' a a' ha2 ha2'

/-! ## o2: the decision function — the type-totality witness (fork 13 correction 2)

TYPE-totality is FREE: a junk/incomplete state gets a TERMINAL fall-back whose full ledger matches
the state, so `ConDecision M s` is inhabited for EVERY `s` (`ConDecision` requires eligibility, not
minimality — the recalibration's "totality" worry dissolves). `leafOfState` is the durable flat-cube
leaf constructor (analytic side empty, chart fields placeholder — the T3-fed content); the real
dispatch (rollover / case-1 eligible-minimal chooser / case-2, with CONE-GOODNESS) layers on top and
is gated on the o1↔o4↔o2 mutual induction (needs `CompChainInv` ⟹ `def4_min` totality). -/

/-- **The flat-cube fall-back leaf** of a state: full ledger `= (numDiv, divExp, divProfile,
cleared)` of the state, flat-cube `srcBox` (the pre-staged `PivotLeafClauses` form), empty analytic
side, placeholder chart data (the T3-fed fields). Its `rootLedger` is the state's by construction —
the terminal `ConDecision`'s `hleaf`. -/
noncomputable def leafOfState (M : Fin (L + 1) → ℕ) (s : ConState L) : LeafData M where
  numDiv := 0
  divExp := Fin.elim0
  cleared := s.cleared
  divProfile := Fin.elim0
  fullNumDiv := s.numDiv
  fullDivExp := s.divExp
  fullDivProfile := s.divProfile
  numB := 0
  bExp := Fin.elim0
  bChain := by intro a _ _; exact a.elim0
  chartMap := id
  srcBox := ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1
  resRank := 0
  divCoord := Fin.elim0
  resCoord := Fin.elim0

/-- **The type-totality witness** (o2, fork 13 correction 2): a TOTAL oracle — always the terminal
fall-back — inhabiting `ConDecision M s` for every `s`. The real dispatch replaces the fall-back on
the reachable cone (cone-goodness, gated); this witnesses that the interface is inhabited. -/
noncomputable def oracleTerminal (M : Fin (L + 1) → ℕ) (s : ConState L) : ConDecision M s :=
  .terminal (leafOfState M s) rfl

/-- `buildTree` with the terminal oracle is a single leaf — the totality witness composes with the
assembly. -/
theorem buildTree_oracleTerminal (M : Fin (L + 1) → ℕ) (s : ConState L) :
    buildTree M (oracleTerminal M) s = ResolutionTree.leaf (leafOfState M s) :=
  buildTree_terminal M (oracleTerminal M) s (leafOfState M s) rfl rfl

/-! ## o2: the Def-4-minimal chooser (total via fallback; min-EXISTENCE gated on o4)

The case-1 chooser (simulator `def4_min`): among the divisors at the target clearing level, select
the componentwise-≤ MINIMUM (Def. 4, p.14). Its DEFINITION is total — `find?` returns the first
componentwise-min, or `none` (the comparability-fallback signal, keeping the oracle type-total). The
min-EXISTENCE — that on a `CompChainInv` state a componentwise-min always EXISTS at any occupied
level, so `none` never fires on the reachable cone — is the o4-certificate content that plugs into
`chooseMin`'s totality (`chooseMin_none_of_compChain` below is its landing pad). -/

/-- **The Def-4 minimal chooser**: the first divisor at clearing level `target` that is
componentwise-`≤` every divisor at that level (Def. 4, p.14). `none` signals no componentwise-min
(the comparability fallback). -/
def chooseMin {L : ℕ} (s : ConState L) (target : ℕ) : Option (Fin s.numDiv) :=
  (List.finRange s.numDiv).find? (fun k => decide
    (s.divTilde k = target ∧
      ∀ k' : Fin s.numDiv, s.divTilde k' = target →
        ∀ j : Fin L, s.divProfile k j ≤ s.divProfile k' j))

/-- **`chooseMin` spec**: a returned divisor is at level `target` AND is Def-4-minimal among the
divisors at that level (componentwise-`≤` all of them). The eligibility + minimality the case-1
emission's `hstep` needs, read straight off the chooser. -/
theorem chooseMin_spec {L : ℕ} (s : ConState L) (target : ℕ) {k : Fin s.numDiv}
    (hk : chooseMin s target = some k) :
    s.divTilde k = target ∧
      ∀ k' : Fin s.numDiv, s.divTilde k' = target →
        ∀ j : Fin L, s.divProfile k j ≤ s.divProfile k' j := by
  have := List.find?_some hk
  simpa using of_decide_eq_true this

/-- **The o4 landing pad**: on a `SameLevelChainInv` state, IF some divisor sits at level `target`,
the chooser does NOT fall back — a componentwise-min exists (the same-level chain makes `def4_min`
total). PROVED below (`chooserTotalOnChain_of_sameLevel`) — the o2 min-existence half of the
mutual induction. -/
def ChooserTotalOnChain {L : ℕ} (s : ConState L) : Prop :=
  ∀ target : ℕ, (∃ k : Fin s.numDiv, s.divTilde k = target) → (chooseMin s target).isSome

/-- **On a chain, a componentwise minimum equals a sum minimum**: if `a`, `b` are Def-4-comparable
and `∑ a ≤ ∑ b`, then `a ≤ b` componentwise. (If `b ≤ a` but `a ≰ b`, some coord is strict, so
`∑ b < ∑ a` — contradicting `∑ a ≤ ∑ b`.) The scalar `∑` witnesses the chain minimum. -/
theorem le_of_comparable_sum_le {L : ℕ} {a b : Fin L → ℕ}
    (hcomp : (∀ j, a j ≤ b j) ∨ (∀ j, b j ≤ a j))
    (hsum : ∑ j, a j ≤ ∑ j, b j) : ∀ j, a j ≤ b j := by
  rcases hcomp with h | h
  · exact h
  · by_contra hcon
    push Not at hcon
    obtain ⟨j, hj⟩ := hcon
    have hlt : ∑ i, b i < ∑ i, a i :=
      Finset.sum_lt_sum (fun i _ => h i) ⟨j, Finset.mem_univ j, hj⟩
    omega

/-- **`ChooserTotalOnChain` PROVED from `SameLevelChainInv`** (o2 min-existence). The eligible set
`{k : t̃ k = target}` is same-level, hence a chain (`hchain`); a `∑`-minimum over it (finite,
nonempty) is therefore a componentwise minimum (`le_of_comparable_sum_le`), which is exactly
`chooseMin`'s `find?` predicate — so the chooser returns it (`isSome`), never the fallback. -/
theorem chooserTotalOnChain_of_sameLevel {L : ℕ} (s : ConState L)
    (hchain : SameLevelChainInv s) : ChooserTotalOnChain s := by
  rintro target ⟨k₀, hk₀⟩
  obtain ⟨k, hkE, hkmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun k => s.divTilde k = target))
    (fun k => ∑ j, s.divProfile k j)
    ⟨k₀, Finset.mem_filter.mpr ⟨Finset.mem_univ k₀, hk₀⟩⟩
  rw [Finset.mem_filter] at hkE
  have hpred : s.divTilde k = target ∧ ∀ k' : Fin s.numDiv, s.divTilde k' = target →
      ∀ j : Fin L, s.divProfile k j ≤ s.divProfile k' j := by
    refine ⟨hkE.2, fun k' hk' j => ?_⟩
    have hcomp := hchain k k' (hkE.2.trans hk'.symm)
    have hsum : ∑ i, s.divProfile k i ≤ ∑ i, s.divProfile k' i :=
      hkmin k' (Finset.mem_filter.mpr ⟨Finset.mem_univ k', hk'⟩)
    exact le_of_comparable_sum_le hcomp hsum j
  rw [Option.isSome_iff_ne_none, Ne, chooseMin, List.find?_eq_none]
  push Not
  exact ⟨k, List.mem_finRange k, by simpa using hpred⟩

/-! ## o2: the dispatch `classify` (simulator `_proc`, indexing pinned `layer = S−1`)

Which step the state admits — the simulator's dispatch, transcribed with `layer = S−1`:
`S = layer+1`, `Mrun(S) = min(M i : i ≤ layer) = widthMinUpto layer`, `MSp1 = min(Mrun(S), M⁽ˢ⁺¹⁾) =
widthMinUpto (layer+1)`. Terminal at `layer = L` (`S = L+1`); else rollover if `J ≥ MSp1`; else
case-1 on the least occupied `t̃`-level in `[J+1, Mrun(S)−1]`; else case-2. Pure/decidable — the
CONE-GOODNESS (this dispatch makes μ-progress on invariant states) is proven separately. -/

/-- Which step a live state admits (the dispatch tag; `case1` carries the target clearing level). -/
inductive StepKind where
  | terminal
  | rollover
  | case1 (target : ℕ)
  | case2
  deriving DecidableEq, Repr

/-- `min(M i : i ≤ n)` — the running-min width through paper layer `n+1` (`= Mrun(n+1)`). Nonempty
(index `0` qualifies), so a `Finset.inf'`. -/
def widthMinUpto (M : Fin (L + 1) → ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (L + 1) => (i : ℕ) ≤ n)).inf'
    ⟨0, by simp⟩ M

/-- **The dispatch** (simulator `_proc`, `layer = S−1`): the step kind the state admits. -/
def classify (M : Fin (L + 1) → ℕ) (s : ConState L) : StepKind :=
  if L ≤ s.layer then .terminal
  else if widthMinUpto M (s.layer + 1) ≤ s.cleared then .rollover
  else
    let occ := (List.finRange s.numDiv).filterMap (fun k =>
      let t := s.divTilde k
      if s.cleared + 1 ≤ t ∧ t + 1 ≤ widthMinUpto M s.layer then some t else none)
    match occ.min? with
    | some target => .case1 target
    | none => .case2

end DLNFibre.DLN.RLCT.Engine
