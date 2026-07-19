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

/-- **The CoV bridge — flat virtual-leaf atlas** (fork 13(o5) type correction, elder-gate8). The old
`⋃ l ∈ leaves t` shape asserted ONE chart per LEDGER leaf; but the ledger tree is the symmetric
QUOTIENT of the geometric fan-out (one ledger leaf stands for a node's full `d_center` pivot family),
and a single per-leaf `chartMap`/`divCoord` cannot carry a family of pivots blowing up different flat
coordinates. The corrected carrier is a FLAT ATLAS: an explicit `List (LeafData M)` of geometric chart
pieces ("virtual leaves"), each with its OWN `chartMap`/`srcBox`/`divCoord`/`divExp`, decoupled from
`leaves t`. LEDGER/ATLAS SPLIT: the ledger (`leaves t`, via `terminalExponents`) carries EXPONENTS; the
atlas carries CHARTS — no clause here reads a ledger leaf's `chartMap`. Clauses:
* (A) IMAGE-COVER over the atlas pieces — an UPSTAIRS-open neighbourhood of the zero-locus inside
  `⋃ c ∈ atlas` (chart IMAGES; a measurable, bounded source box each);
* (B) the eight per-piece clauses — measurable + bounded-in-flat-cube `srcBox`, injective/disjoint
  divisor & Morse coordinates (finding 5), a.e.-injectivity off a null set (finding 6 — a blow-up chart
  is not injective on the exceptional fibre), `LeafPullback` + `LeafJacobian`; each reads the piece's
  OWN chart, so per-pivot `divCoord` dissolves the frozen type's piecewise failure;
* (C) EXPONENT-AGREEMENT — each piece's `divExp` and positive `resRank` lie in `terminalExponents t`
  (LOAD-BEARING: the atlas is decoupled from `leaves t`, so this replaces the old automatic
  `flatMap`-over-`leaves t` routing, feeding exactly the two threshold hypotheses of
  `leaf_chart_image_lintegral_lt_top`).
HONEST FORM (the (D)-less window): (A)∧(B)∧(C) guarantee only that the atlas is A MONOMIALISING COVER
WHOSE EXPONENTS AGREE WITH `t` — NOT yet that it is `t`'s resolution charts. That fidelity tie is
exactly DEFERRED clause (D) — fidelity coherence (NOT consumed by `region_glue`; elder-pinned CONTENT,
encoding deferred to me for the carrier phase): each atlas piece's `chartMap` is the REAL `β∘ψ`
geometric fold of a `t`-path (a `geometricLeafPaths t` analog + the banked `pivotChart`/gauge atoms —
never an opaque `Params M → Params M`; two-sided honesty: provable over the constructed atlas, false on
a generic one). GATE (cordon-checked): (D) must be IN this type BEFORE `chartBridge_buildTree`'s
discharge lands — a proven discharge against a (D)-less type would close the hole with the "`t`'s cover"
tie missing. (D) lands additively (a def-only touch; `region_glue` and the `CanonicalResolution`
projection are agnostic to it). -/
def ChartBridge (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  ∃ atlas : List (LeafData M),
    (∃ U : Set (Params M), IsOpen U ∧
        {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
        U ⊆ ⋃ c ∈ atlas, c.chartMap '' c.srcBox) ∧
    (∀ c ∈ atlas,
      MeasurableSet c.srcBox ∧
        (∃ R : ℝ, 0 < R ∧ c.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) ∧
        Function.Injective c.divCoord ∧ Function.Injective c.resCoord ∧
        Disjoint (Set.range c.divCoord) (Set.range c.resCoord) ∧
        (∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (c.srcBox \ N)) ∧
        LeafPullback c ∧ LeafJacobian c) ∧
    (∀ c ∈ atlas, (∀ k : Fin c.numDiv, c.divExp k ∈ ResolutionTree.terminalExponents t) ∧
      (0 < c.resRank → c.resRank ∈ ResolutionTree.terminalExponents t))

/-- **The running-min corank** `M(i+1) = min(M⁽¹⁾ … M⁽ⁱ⁺¹⁾)` at head index `p` (0-indexed, so the
1-indexed layer `i = p+1`): the min of the widths `M 0 … M p.succ`. FIX-A (below) caps the Case-2
head-reset at this, not the RAW `M p.succ`. -/
def runMinWidth (M : Fin (L + 1) → ℕ) (p : Fin L) : ℕ :=
  (Finset.Iic p.succ).inf' ⟨p.succ, Finset.mem_Iic.mpr le_rfl⟩ M

/-- `min(M i : i ≤ n)` — the running-min width through paper layer `n+1` (`= Mrun(n+1)`; it is
`Mrun(S)` at `n = layer = S−1`). Nonempty (index `0` qualifies), so a `Finset.inf'`. Lives here (not
`EngineConstruction`) because the rollover-edge at-exhaustion guard in `StepRel` below reads it — the
guard is pinned to the construction dispatch's rollover trigger `widthMinUpto (layer+1) ≤ cleared`. -/
def widthMinUpto (M : Fin (L + 1) → ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (L + 1) => (i : ℕ) ≤ n)).inf' ⟨0, by simp⟩ M

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
  | StepCase.rollover =>
      -- LAYER ROLLOVER (Aoyagi p.21 block-exhaustion reindexing `S → S+1`): a CHARTLESS relabel. The
      -- divisor ledger (`numDiv`/`divExp`/`divProfile`) carries over UNCHANGED; only the per-layer
      -- cleared count resets (`J := 0`). No coordinate change (the pure-(a) rollover gauge,
      -- design §7 — `localSub = id`). The node's `layer` (dropped by `RootLedger`) advances on the
      -- child; `StepRel`'s eligibility ∨ exempts a rollover edge (not case11/case12), so it stays
      -- rfl-class. Matches `ConState.stepRollover`'s `toRootLedger` exactly.
      { numDiv := n.numDiv
        divExp := n.divExp
        divProfile := n.divProfile
        cleared := 0 }

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
each child ledger via `stepUpdate`, the equality is rfl-class.
THIRD CONJUNCT — the ROLLOVER AT-EXHAUSTION GUARD (elder-gate6, compass 13(Q3); fork-9 mandate): a
`rollover` edge is faithful only when the parent layer is EXHAUSTED, `widthMinUpto M (n.layer+1) ≤
n.cleared` (`J ≥ Mrun(S+1)`). WITHOUT it `StepRel` would bless an EARLY rollover stranding pending
divisors — a ledger-consistent NON-Aoyagi tree caught only by `ChartBridge`'s semantic falsity, the
exact infidelity class fork 9 rejects at the ledger (`earlyRollover_not_stepRel`). The comparison is
pinned to the simulator-validated construction dispatch's rollover trigger (`classify`), not a page
off-by-one. Vacuous for case11/case12/case2 (they are not `rollover`), so the ledger equality stays
rfl-class and the eligibility clause is unchanged. -/
def StepRel {M : Fin (L + 1) → ℕ} (n : StepData M) (e : Edge M) : Prop :=
  ResolutionTree.rootLedger e.child = stepUpdate n e.case e.subst ∧
    ((e.case = StepCase.case11 ∨ e.case = StepCase.case12) →
      ∃ h : e.subst.mergeIdx < n.numDiv,
        n.divTilde ⟨e.subst.mergeIdx, h⟩ = n.cleared + e.subst.runLen) ∧
    (e.case = StepCase.rollover → widthMinUpto M (n.layer + 1) ≤ n.cleared)

/-- **Full monomialisation** (B'): each leaf's ANALYTIC (`t̃=0`) divisor exponent equals `Mval` of
its rank profile, AND that profile is ADMISSIBLE (`divProfile k ∈ Adm M`; note `∈ Adm` gives
last-component-`0`, so `t̃ = min = 0` — the analytic read-off IS over `t̃=0` divisors, for free). PLUS
the B' COHERENCE TIE (VALUE/SUPPORT level): each analytic divisor's `(divExp, divProfile)` matches a
`t̃=0` full divisor, and every `t̃=0` full divisor is matched — so the analytic side and the `t̃=0`
full sublist have EQUAL VALUE-SUPPORT. C2/C3 forget multiplicity (duplicate values may collapse);
the `leafOfState` construction IS a genuine index sublist, but the PREDICATE promises only set-level
equality — enough for the support-only `terminalExponents` min (nothing missed, nothing spurious),
not for a multiplicity-sensitive consumer. The leaf chain is enforced at type strength by
`LeafData.bChain`. -/
def IsFullMonomialization {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : Prop :=
  ∀ l ∈ ResolutionTree.leaves t,
    (∀ k : Fin l.numDiv, l.divExp k = (Mval M (l.divProfile k)).toNat ∧ l.divProfile k ∈ Adm M) ∧
      (∀ k : Fin l.numDiv, ∃ j : Fin l.fullNumDiv,
        l.divExp k = l.fullDivExp j ∧ l.divProfile k = l.fullDivProfile j ∧
          tildeOf (l.fullDivProfile j) = 0) ∧
      (∀ j : Fin l.fullNumDiv, tildeOf (l.fullDivProfile j) = 0 →
        ∃ k : Fin l.numDiv, l.divExp k = l.fullDivExp j ∧ l.divProfile k = l.fullDivProfile j)

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
