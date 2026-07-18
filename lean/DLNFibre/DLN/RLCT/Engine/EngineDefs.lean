import DLNFibre.DLN.RLCT.Engine.ResolutionTree
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineDefs` — the engine's carrier-facing definitions

**Blueprint spine: statements are forecasts; churn is normal.** The `def`s the transform-only Aoyagi
engine's obligations rest on, SPLIT OUT from the sorried theorems (`EngineObligations`) so the
consumers — the region-glue lane in particular — can import `ChartBridge`/`LeafPullback`/
`LeafJacobian`/`residualBaseForm` and the carrier-facing transition defs WITHOUT pulling in the
sorried `monomialization_terminates` / `region_glue`. `EngineObligations` imports this file and MAY
import glue modules; this file imports neither.

Key shapes (cert-carrier-review + council amendments):
* `StepRel` READS `e.child` (root accessors) + `e.subst.runLen` and requires the case-specific CHILD
  update; the case-1(1)/1(2) eligibility conjunct guards both (elder-confirmed, Aoyagi p.15).
* `terminalExponents` folds in every positive `resRank` (ruling 2a).
* `LeafJacobian` is the FACTORED form `chartMap = ψ ∘ β` (ruling 2b, fork-8 area-formula revision).
* `ChartBridge` — measurable/bounded/injective-disjoint coords, a.e.-injectivity, `LeafPullback` +
  `LeafJacobian`, derived-fold coherence.
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

/-- **The Jacobian ledger — FACTORED form** (ruling 2b, fork 8, area-formula revision). `chartMap =
ψ ∘ β` on the source box, where `β` is the explicit monomial blow-up (`|det Dβ| = ∏ |u|^{divExp−1}`,
abs-value — finding 7; handled by direct monomial integration / the scaling bridge) and `ψ` is a
bounded-unit local diffeomorphism. The per-leaf read (elder-ratified fork-8 revision) is the Mathlib
AREA FORMULA, which consumes only `ψ`'s UPPER determinant bound `|det Dψ| ≤ hi`; the banked
`rlctAtOn_boundedUnit_localHomeomorph` transport is unused, so the extra inverse data (`ψsymm`,
inverse identities, the lower bound) is carried but not load-bearing. `β` is Aoyagi's
monomialized-integrand chart; the read was never meant to eat the singular factor. -/
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
zero locus via chart IMAGES; every leaf chart has a MEASURABLE, BOUNDED-in-flat-cube source box
(elder-ratified strengthening — an unbounded `srcBox` provably breaks `region_glue`'s per-coordinate
threshold, glue-lane counterexample), injective/disjoint divisor & Morse coordinates (finding 5), is
A.E.-INJECTIVE off a null set (finding 6 — a blow-up chart is not injective on the exceptional
fibre), and satisfies `LeafPullback` + `LeafJacobian`; and each leaf's `chartMap` is the DERIVED
fold of its root→leaf edge substitutions (coherence). -/
def ChartBridge (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  (∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartMap '' l.srcBox) ∧
    (∀ l ∈ ResolutionTree.leaves t,
      MeasurableSet l.srcBox ∧
        (∃ R : ℝ, 0 < R ∧ l.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) ∧
        Function.Injective l.divCoord ∧ Function.Injective l.resCoord ∧
        Disjoint (Set.range l.divCoord) (Set.range l.resCoord) ∧
        (∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn l.chartMap (l.srcBox \ N)) ∧
        LeafPullback l ∧ LeafJacobian l) ∧
    (∀ p ∈ ResolutionTree.leafPaths (id : Params M → Params M) t, p.1.chartMap = p.2)

/-- **The running-min corank** `M(i+1) = min(M⁽¹⁾ … M⁽ⁱ⁺¹⁾)` at head index `p` (0-indexed, so the
1-indexed layer `i = p+1`): the min of the widths `M 0 … M p.succ`. FIX-A (below) caps the Case-2
head-reset at this, not the RAW `M p.succ`. -/
def runMinWidth (M : Fin (L + 1) → ℕ) (p : Fin L) : ℕ :=
  (Finset.Iic p.succ).inf' ⟨p.succ, Finset.mem_Iic.mpr le_rfl⟩ M

/-- **The typed transition** (rung 1, fork 9): the child root ledger CORE a step DETERMINES from its
parent `n`, the `case`, and the edge substitution `σ` — `numDiv`, per-divisor `divExp`/`divTilde`,
`cleared`. Faithful to the page-image transitions:
* **case 1(1)** — merge INTO divisor `σ.mergeIdx`: its exponent `+= runLen·resCols`
  (`M' = M + J₁·(M^{(S+1)}−J)`, preprint p.16), its `t̃ → cleared`; `numDiv`/`cleared` unchanged.
* **case 1(2)** — SPLIT divisor `σ.mergeIdx` into a NEW pivot appended at the end with exponent
  `divExp(mergeIdx) + runLen·resCols` and `t̃ = cleared` (preprint p.17 `M'_{S,J+1} = M_{sk} +
  J₁·(M^{(S+1)}−J)`, `t̃_{S,J+1}=J`); advance `cleared` by one.
* **case 2** — append a NEW pivot divisor of exponent `resRows·resCols` (preprint p.20) with
  `t̃ = cleared`; advance `cleared` by one, like case 1(2) (elder p.21: J increases by ONE per
  Case-2 step — the full block clears over SUCCESSIVE Case-2 steps, each a distinct pivot of
  strictly smaller exponent `(M(S)−J−i)(M^{(S+1)}−J−i)`; a `+= resRows` fast-forward would DROP
  those divisors, one of which can be the binding minimum).
SUPPORT PROPAGATION is STOP-AND-SURFACEd (NOT modelled here): transporting the `support` `Finset`s
across the per-divisor re-indexing balloons (Codex-confirmed; compass second cost center), deferred
to the named `genDivExp` redesign rung. The transitions are page-pinned to the AOYAGI preprint
(`aoyagi-2023-neural-networks-preprint.pdf`, NOT Lehalleur-Rimányi): case-1(1) merge p.16; case-1(2)
exponent p.17; case-2 exponent p.20 + `cleared+1` p.21; case-1 eligibility p.15. -/
def stepUpdate {M : Fin (L + 1) → ℕ} (n : StepData M) (c : StepCase) (σ : ChartSubst M) :
    ResolutionTree.RootLedger L :=
  -- `T`-rule tail-write (rung R1, pnp-atlas verdict 3): the tail `t⁽ˢ⁾…⁽ᴸ⁾ := J`. Fixed index set
  -- `{1..L}`, no re-indexing. INDEXING (trace-`S` 1-indexed ↔ Lean `layer` 0-indexed): tail iff
  -- `n.layer ≤ p.val`. The head is per-case (unchanged / inherited / width-reset).
  let setTail : (Fin L → ℕ) → (Fin L → ℕ) :=
    fun T p => if n.layer ≤ (p : ℕ) then n.cleared else T p
  match c with
  | StepCase.case11 =>
      -- mutate the fixed divisor `mergeIdx`: head UNCHANGED, tail `:= J` (Aoyagi p.16)
      { numDiv := n.numDiv
        divExp := fun k => if (k : ℕ) = σ.mergeIdx then n.divExp k + σ.runLen * n.resCols
                            else n.divExp k
        divProfile := fun k => if (k : ℕ) = σ.mergeIdx then setTail (n.divProfile k)
                                else n.divProfile k
        cleared := n.cleared }
  | StepCase.case12 =>
      -- new pivot: head INHERITED from the parent divisor `mergeIdx`, tail `:= J` (Aoyagi p.17)
      { numDiv := n.numDiv + 1
        divExp := Fin.snoc n.divExp
          ((if h : σ.mergeIdx < n.numDiv then n.divExp ⟨σ.mergeIdx, h⟩ else 0)
            + σ.runLen * n.resCols)
        divProfile := Fin.snoc n.divProfile
          (setTail (if h : σ.mergeIdx < n.numDiv then n.divProfile ⟨σ.mergeIdx, h⟩ else fun _ => 0))
        cleared := n.cleared + 1 }
  | StepCase.case2 =>
      -- new pivot: head RESET to the RUNNING-MIN width `t⁽ⁱ⁾ := M(i+1) = min(M⁽¹⁾…M⁽ⁱ⁺¹⁾)`
      -- (`runMinWidth`), tail `:= J`. DEVIATION-FROM-PAGE (FIX-A): Aoyagi p.20 prints the RAW
      -- `M⁽ⁱ⁺¹⁾`, but that label disagrees with the SAME step's running-min exponent at
      -- non-monotone widths (label≠exponent at (2,2,3,2); a verified defect, Def-3's class — see
      -- theory/aoyagi-2023-reproduction/verify-case2-rawwidth-defect.md). The cap restores
      -- label==exponent + an Adm-clean t̃=0 atlas; invisible at monotone widths / L ≤ 2.
      { numDiv := n.numDiv + 1
        divExp := Fin.snoc n.divExp (n.resRows * n.resCols)
        divProfile := Fin.snoc n.divProfile (setTail (fun p => runMinWidth M p))
        cleared := n.cleared + 1 }

/-- **The faithful per-step transition relation** (rung 1). FAITHFUL for the exponent/clearing
ledger CORE (`numDiv`/`divExp`/`divTilde`/`cleared`): the child's root ledger EQUALS the parent's
`stepUpdate`, AND — for BOTH case-1(1) and case-1(2), the two charts of the SAME case-1 blow-up on
`u_{s,k}` — the merge/split target is ELIGIBLE: `σ.mergeIdx` in range with `t̃_{mergeIdx} = J + J₁`.
Elder-CONFIRMED from the Aoyagi preprint page images: Case 1 fixes ONE divisor `u_{s,k}` with
`t̃_{s,k} = J + J₁` (p.15) BEFORE the 1(1)/1(2) split, and case-1(2)'s base `M_{sk}` is that same
divisor's exponent (`u_{s,k} = u_{S,J+1}·u'_{s,k}`, p.17) — so the identical conjunct is faithful
for both. The in-range half is also mechanically required for case12: `stepUpdate` case12 reads
`divExp(mergeIdx)` as the split pivot's base, and an OUT-OF-RANGE `mergeIdx` silently `dite`-drops
it to `0` — accepted without this guard (`oobSplit_not_stepRel`).
DELIBERATELY UNCAPTURED (shared by case11; the divisor-chooser's burden at rung 3-4, named so they
do not vanish): (i) the MINIMALITY tie-break — p.15 selects `u_{s,k}` lexicographically-minimal
(`T_{s,k} ≤ T_{s',k'}` for all `t̃_{s',k'} = J+J₁`, Def. 4 p.14); this conjunct pins the clearing
LEVEL, not the min-SELECTION; (ii) the GAP CONDITION defining `J₁` — `{t̃_{s,k} = i} = ∅` for
`i = J+1,…,J+J₁−1` (`runLen = J₁` is the run to the next occupied level); the encoding takes
`runLen` as given. Also NOT modelled here: support propagation (folds into the `genDivExp` carrier
at R1; propagation proofs at R4) and layer-`S` advancement (lives in the construction's `State`, the
μ 1st component). Retires the existential form — a dummy divisor appearing/vanishing changes
`rootLedger e.child` and is rejected (`dummyDivisor_not_stepRel`). Since the construction computes
each child ledger via `stepUpdate`, the equality is rfl-class. -/
def StepRel {M : Fin (L + 1) → ℕ} (n : StepData M) (e : Edge M) : Prop :=
  ResolutionTree.rootLedger e.child = stepUpdate n e.case e.subst ∧
    ((e.case = StepCase.case11 ∨ e.case = StepCase.case12) →
      ∃ h : e.subst.mergeIdx < n.numDiv,
        n.divTilde ⟨e.subst.mergeIdx, h⟩ = n.cleared + e.subst.runLen)

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

end DLNFibre.DLN.RLCT.Engine
