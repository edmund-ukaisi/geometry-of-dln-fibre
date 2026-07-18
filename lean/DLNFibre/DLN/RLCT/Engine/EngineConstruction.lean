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

/-- **The state invariant** (rung 2; shape-locked, detail loose). The layer has not overshot the
chain (`S ≤ L`) and the cleared count has not overshot the within-layer ceiling (`J ≤ layerCap`).
These are the facts the descent lemmas' strict preconditions refine (a rollover needs `S ≤ L`; a
`J`-advancing step needs `J < layerCap`). -/
structure StateInvariant (M : Fin (L + 1) → ℕ) (s : ConState L) : Prop where
  /-- The layer has not overshot the chain. -/
  layer_le : s.layer ≤ L
  /-- The cleared count has not overshot the within-layer ceiling. -/
  cleared_le : s.cleared ≤ layerCap M

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
  /-- Step: emit a node (ledger core `= s`'s) with `conRel`-smaller children. `rootLedger` on a
  `branch` ignores the edges, so the guarantee is stated on the node's ledger core directly. -/
  | step (node : StepData M) (children : List (StepChild M s))
      (hnode : (⟨node.numDiv, node.divExp, node.divProfile, node.cleared⟩ :
          ResolutionTree.RootLedger L) = s.toRootLedger) :
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
    | .step node children _ =>
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
  | step node children hnode => exact hnode

/-! ## T2 build-side invariants (TYPES only; preservation proofs are buildTree bricks) -/

/-- **The weakened per-node invariant** (elder-gate4 §3a). Each divisor's rank-pattern is
WEAK-DECREASING (`t⁽¹⁾ ≥ … ≥ t⁽ᴸ⁾`) and BLOCK-BOUNDED (`t⁽ʲ⁾ ≤ admBound M j`). This — NOT
`divProfile ∈ Adm` — is what the T-rule preserves per node: a PENDING node has `t̃ = min T > 0`, so
its last component `> 0` and it is NOT in `Adm` (clause 3). `∈ Adm` is the LEAF property
`WeakProfileInv + leaf-t̃=0` (post-final-rollover `J=0`). The preservation lemma
`stepUpdate_preserves_weakInv` is a buildTree brick; the case-2 raw-width reset at non-monotone
widths is the pnp (2,2,3,2) gate. -/
def WeakProfileInv (M : Fin (L + 1) → ℕ) (s : ConState L) : Prop :=
  ∀ k : Fin s.numDiv,
    (∀ i j : Fin L, i ≤ j → s.divProfile k j ≤ s.divProfile k i) ∧
      (∀ j : Fin L, s.divProfile k j ≤ admBound M j)

/-- **The total-comparability CHAIN invariant** (elder-gate4 §3c). The carried profiles are pairwise
Def-4-comparable (`T_k ≤ T_{k'}` or `T_{k'} ≤ T_k`, componentwise) — the maintained chain, NOT
merely the chooser's local minimality. T3's cover proof CONSUMES this (invariant→principalization,
`cert-atlas-probe-2222` (c)); its preservation is a buildTree brick. -/
def CompChainInv {L : ℕ} (s : ConState L) : Prop :=
  ∀ k k' : Fin s.numDiv,
    (∀ j : Fin L, s.divProfile k j ≤ s.divProfile k' j) ∨
      (∀ j : Fin L, s.divProfile k' j ≤ s.divProfile k j)

end DLNFibre.DLN.RLCT.Engine
