import DLNFibre.DLN.Aoyagi.Case1Wire
import DLNFibre.DLN.Aoyagi.SourceClearedResid
import DLNFibre.DLN.Aoyagi.MergeBoostSplit

/-!
# `DLNFibre.DLN.Aoyagi.ClearedFold` — THE GLOBAL MOVE: the fold-invariant chain on the cleared object

The wall's boost-center property `Deg1SupportedOn … ed.center` (property **(D)**) is FALSE on the raw
shears-only `foldResid` (the (2,2,2,2) `u₀₁₀` obstruction) and TRUE on the **source-cleared** chart
residual `sourceClearedResid` (`SourceClearedResid.lean`). This module RESTATES the fold-invariant
chain — the accumulated coordinate change, dominant monomial, and step invariant — on the cleared
objects, so the wall's case-1(1) branch is discharged on the object the property actually holds of.

**THE PRECOMPOSE FORM (frame §6/§7, pnp 816f5de19 + her-order check 0577aa9c7, both controller-re-ran
exit 0 — UNCONDITIONAL).** The faithful cleared fold is the raw trio precomposed with CAPR's
`couplingClear` (global source-clear on the input, THEN the blow-up path):

* `clearedFoldG d p := foldG d (canonFlatten d) p ∘ couplingClear d p`
* `clearedFoldB d p := foldB d (canonFlatten d) p ∘ couplingClear d p` — a clean **monomial**
  `∏(δ=1 pivots)` at every node (the pivot factor lives in the B-side by construction).
* `clearedFoldResid = sourceClearedResid` (CAPR — `foldResid ∘ couplingClear`).

A per-step interleaved clear-before-blow-up does NOT equal the precompose (false at every node), and
Aoyagi's literal blow-up-THEN-clear order also does not (our `canonNormalizationOf` shear reads the raw
coupling, so a post-blow-up clear arrives too late). So there is no per-step recursion variant; the
precompose is the faithful rendering of her cleared recursion in our shear-coordinates.

**FIDELITY (elder-blessed, certificate §10; the cross-ref-honesty gate).** `sourceClearedResid` is
Aoyagi's cleared residual block `D_J` **RLCT-equivalent via the source-clear rendering (coordinate-form
differs by our shear-frame)** — NOT bit-identical to her literal `Q`,`P` image; coordinate-identity is a
right-extension, not a fidelity gate (her Lemma 1 treats RLCT-equivalent representatives as one object).
Every cross-reference to `aoyagi-2023-worked.tex` in this module states the relationship at that precision.

**THE (iv) Q₁-LIFT BRIDGE is CONSUMED, not re-declared** — `rlctGlobal(∑foldResid²) =
rlctGlobal(∑sourceClearedResid²)` is CAPR's `SourceClearedResid.rlctGlobal_sumSqFam_foldResid_eq_sourceCleared`
(the det-1 parameter-space gauge; the read-off runs on the cleared object, the raw recursion supplies the
`∏A` value, and this bridge reconciles the payoff — character unchanged). This module does NOT restate it.

**SCOPE / OWNERSHIP.** The raw fold trio (`foldG`/`foldB`/`foldResid`) and the recursion are UNCHANGED
(Option 2′). This module is DOWNSTREAM of `Case1Wire` (reuses its reusable per-edge lemmas) and produces
the cleared analogues of the case-1 preservation chain. The genuinely-new-math content lemma (the cleared
case11 boost-split, `MergeBoostSplit.foldResid_case11_mergeBoostSplit_sourceCleared`) is CAPR's induction
target (#72); this module CONSUMES it via `realBranch_boostReady_case11'`. The consumer re-points in
`Case1Wire`/`CaseStepAssembly`/`LastLayerWire`/`MonumentAssembly` are listed in the SPECIFY message (in-place
edits, per-file go); the aggregator wire is the controller's integration unit (#73).

**THE PROVENANCE LAYER — DEFERRED (written, not silent; charter-§3).** `GeoAtlasData` / `FoldProduced` /
`FoldRealizes` (which pins `atlas.gmap c = foldG d e (pathOf c)`) / the leaf shape
`PrincipalInv (coreGen d e) (atlas.gmap c) …` — whether these SURVIVE raw or RE-STATE on `C` — is NOT
decided by this unit. This unit leaves the provenance layer RAW and UNTOUCHED at the statement level: the
summit `leaf_stepInv_of_path'` is invariant-free with a sorried body, so the cleared invariant enters only
through its cone-registration `have`s, and re-pointing them keeps the summit type-stable and the build green
(the payoff `aoyagi_learning_coefficient_L1` avoids the summit and stays clean-three). §8's "summit consumes
the cleared invariant" is satisfied at the PROOF-SCAFFOLD layer (the `have`s); the OUTPUT-ATLAS layer is a
separate question with a genuine tension (`couplingClear` is non-invertible, so a cleared atlas may not be a
valid resolution atlas; the (iv) Q₁-lift is an rlctGlobal-level bridge, not a per-chart CoV; L4D found no
per-node bridge). OWNER of the survive-vs-restate decision: the **L5 fold-body SPECIFY author**. RE-OPEN
TRIGGER: **L5 fold-body SPECIFY time**. Elder-ratified at this unit's SPECIFY delta-read.

**THE RAW `realBranch_appendResidDescent` SITES — OUTSIDE this unit.** The conjunct-B descent frontier
(`MonumentAtlas.realBranch_appendResidDescent` + its `MultiAffineStepWire` consumers) resolves via the
cap-transport hinge (verdict TRANSPORTS, `cap-frontier-certificate.md` §6 / #78: cleared-(b) = the raw
UNCAPPED descent ∘ `couplingClear`, a function-level kill). A parallel seat (seat-CAPF) renders the raw
uncapped descent + kill lemma + a primed (b)-twin; the swap lands at integration. This unit neither deletes
nor re-points the raw descent sites; the cleared conjunct-B step here (`realBranch_multiAffine_step_cleared`)
is a frontier that CONSUMES the cleared descent (seat-CAPF's twin) at integration.

STATUS: SPECIFY skeleton — signatures validated, proofs are the PROOFS phase. Every substantive body is a
tracked `-- map:` frontier (`B-globalmove-*`); the trivial region/continuity/root facts are marked
`SPECIFY-trivial`. -/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-! ### §1 The cleared trio (precompose form) -/

/-- **`clearedFoldG d p := foldG d (canonFlatten d) p ∘ couplingClear d p`** — the accumulated coordinate
change read on the ancestor-cleared input. -/
noncomputable def clearedFoldG (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  fun u => foldG d (canonFlatten d) p (couplingClear d p u)

/-- **`clearedFoldB d p := foldB d (canonFlatten d) p ∘ couplingClear d p`** — the accumulated dominant
monomial `∏(δ=1 pivots)` read on the ancestor-cleared input. Clean monomial at every node. -/
noncomputable def clearedFoldB (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    (Fin (flatDim d) → ℝ) → ℝ :=
  fun u => foldB d (canonFlatten d) p (couplingClear d p u)

/-- **The cleared fold-state step invariant at a node, PARAMETRIC in the center `C`** (the (i)-core). The
cleared analogue of `MonumentAtlas.FoldStepInvAt`, on the cleared trio: (1) a divisibility witness `q` for
the accumulated cleared `StepInv`; (2) the cleared residual is `Deg1SupportedSlot` on `C`. Pinned to
`canonFlatten d` (the cleared story is canonFlatten-specific, matching `sourceClearedResid`). -/
def FoldStepInvAt_cleared (d : Fin (N + 1) → ℕ)
    (C : Finset (Fin (flatDim d))) (p : TreePath d) : Prop :=
  (∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ,
    StepInv (coreGen d (canonFlatten d)) (clearedFoldG d p) (clearedFoldB d p)
      (sourceClearedResid d p) q (foldRegion d (canonFlatten d) p)) ∧
    (∀ j, Deg1SupportedSlot d (sourceClearedResid d p) j C (supportLayerOf p.conState)
      (foldRegion d (canonFlatten d) p))

/-- **The cleared LAST-LAYER (S=L) mixed invariant** (elder 1-bis / #83 — the last-layer cleared route).
The cleared analogue of `MonumentAtlas.LastLayerInv`, on the cleared trio: the accumulated cleared `StepInv`
divisibility, AND a per-slot DISJUNCTION — each cleared residual slot is either `Deg1SupportedSlot` (an
uncleared slot) OR a unit nonvanishing at `0` (a cleared slot). Needed because the last-layer conjunct-A's
case11 branch (`LastLayerWire.lastLayer_conjA` :145) consumes the boost-center `(D)`, which is FALSE on raw
`foldResid` — so the last-layer route re-points to the cleared object exactly like the interior route. The
born-unit value at `0` is UNCHANGED under the clear (`couplingClear d p 0 = 0`, so
`sourceClearedResid d p j 0 = foldResid d (canonFlatten d) p j 0`), so `GeneratorCleared`'s at-origin datum
transports trivially. -/
def LastLayerInv_cleared (d : Fin (N + 1) → ℕ)
    (C : Finset (Fin (flatDim d))) (p : TreePath d) : Prop :=
  (∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ,
    StepInv (coreGen d (canonFlatten d)) (clearedFoldG d p) (clearedFoldB d p)
      (sourceClearedResid d p) q (foldRegion d (canonFlatten d) p)) ∧
    (∀ j : Fin (foldNR d p),
      Deg1SupportedSlot d (sourceClearedResid d p) j C (supportLayerOf p.conState)
          (foldRegion d (canonFlatten d) p) ∨
        (∃ unit : (Fin (flatDim d) → ℝ) → ℝ,
          ContinuousOn unit (foldRegion d (canonFlatten d) p) ∧ unit 0 ≠ 0 ∧
            ∀ u ∈ foldRegion d (canonFlatten d) p, sourceClearedResid d p j u = unit u))

/-! ### §2 Region / continuity of `couplingClear` (controller delta 1 — STATED, not implicit) -/

/-- **`couplingClear` fixes the origin** — SPECIFY-trivial (`0 k` is `0` on both branches of the `if`). -/
theorem couplingClear_zero (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    couplingClear d p 0 = 0 := by
  -- SPECIFY-trivial (proven in PROOFS phase)
  funext k; simp [couplingClear]

/-- **`couplingClear` is continuous** — SPECIFY-trivial (per-coordinate: constant `0` or a projection). -/
theorem continuous_couplingClear (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    Continuous (couplingClear d p) := by
  -- SPECIFY-trivial (proven in PROOFS phase)
  apply continuous_pi; intro k
  by_cases hk : k ∈ couplingCoords d p
  · simp only [couplingClear, if_pos hk]; exact continuous_const
  · simp only [couplingClear, if_neg hk]; exact continuous_apply k

/-- **`couplingClear` maps the certificate region into itself** (controller delta 1: the region
obligation, STATED). Trivial at the `foldRegion = univ` stand-in — kept explicit so the cleared
statements never assume the region-mapping implicitly. -/
theorem couplingClear_mapsTo_foldRegion (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    Set.MapsTo (couplingClear d p) (foldRegion d (canonFlatten d) p)
      (foldRegion d (canonFlatten d) p) := by
  -- SPECIFY-trivial (proven in PROOFS phase; foldRegion = univ)
  rw [foldRegion_eq_univ]; exact Set.mapsTo_univ _ _

/-! ### §3 Root reduction + the monomial B-recurrence -/

/-- **Root reduction** — at the root the cleared trio's `G`/`B` are the raw ones (ancestor-clear empty).
SPECIFY-trivial (`couplingCoords .root = ∅`, so `couplingClear .root = id`). -/
theorem clearedFoldG_root (d : Fin (N + 1) → ℕ) :
    clearedFoldG d (.root : TreePath d) = id := by
  -- SPECIFY-trivial (proven in PROOFS phase)
  sorry

/-- Root reduction for `clearedFoldB`. SPECIFY-trivial. -/
theorem clearedFoldB_root (d : Fin (N + 1) → ℕ) :
    clearedFoldB d (.root : TreePath d) = fun _ => 1 := by
  -- SPECIFY-trivial (proven in PROOFS phase)
  sorry

/-! ### §4 The cleared-locus commutation core (REVISED — O2 finding 20bc71f1d)

**O2 CLOSED WITH A STATEMENT-CLASS FINDING (removed here).** Three naive cleared-trio one-step laws are
FALSE at case2/case12 δ=1 GROWTH edges, where `couplingCoords` grows by the fresh `belowPivotCol` and hence
`couplingClear (p.extend ed) ≠ couplingClear p`: the M-level commutation
`stepMap ∘ couplingClear(child) = couplingClear(parent) ∘ stepMap`, the law
`clearedFoldG(child) = clearedFoldG(parent) ∘ stepMap`, and
`clearedFoldB(child) u = u_pivot^δ · clearedFoldB(parent)(stepMap u)`. They hold at case11 (no growth) and
fail at growth (pnp per-node). REMOVED (a sorry with a wrong statement misleads); the correct route is the
cleared-locus argument.

**THE CLEARED-LOCUS ROUTE (controller-prescribed, pnp-standby-verified).** `FoldStepInvAt_cleared` (S1) is
the RAW StepInv identity restricted to the locus `L_p = {u | ∀ k ∈ couplingCoords d p, u k = 0}` (the
fixed-set of `couplingClear d p`), where the raw obstruction terms carry coupling factors and VANISH — so
S1 holds at every node. The preservation `S1(parent) → S1(child)` runs ON the locus, via:
* `couplingCoords_mono_extend` — `couplingCoords d p ⊆ couplingCoords d (p.extend ed)`, i.e. `L_child ⊆
  L_parent` (the parent's identity restricts to the child's locus FOR FREE at growth edges);
* the RAW one-step laws (`foldG (p.extend ed) = foldG p ∘ stepMap` definitionally, `foldB_extend_eq`,
  `foldResid_extend_delta1/0`) — TRUE, in `MonumentAtlas`/`Case1Wire`, unchanged;
* `couplingClear_parent_fixes_stepMap_child` — `stepMap (couplingClear(child) u) ∈ L_parent` (the ancestor
  couplings are spectators of the current step's shear+blow-up), so the parent's cleared `G`/`B` read it
  unchanged (the load-bearing LOCUS CONTAINMENT that replaces the false commutation);
* `pivot_notMem_couplingCoords_extend` — `ed.pivot ∉ couplingCoords d (p.extend ed)` (pivot is a diagonal
  corner, couplingCoords are strictly below-diagonal), so `(couplingClear(child) u) ed.pivot = u ed.pivot`
  (the `foldB_extend_eq` pivot factor survives the clear — the clean-monomial B-side);
* `sourceClearedResid_extend_delta1/delta0` (S2, below) — TRUE at every node, the residual side.

pnp stands by to verify `couplingClear_parent_fixes_stepMap_child` (the load-bearing containment) + this
induction shape. OWNERSHIP (O1): mine to state AND prove; relocated to the substrate at integration. -/

/-- **couplingCoords stability under a case11 extension** — a case11 step adds no `belowPivotCol` (a MERGE
into an existing exceptional, not a fresh clear), so `couplingCoords d (p.extend ed) = couplingCoords d p`.
SPECIFY-trivial (the `couplingCoords` step arm's case11 match is `∅`, `S ∪ ∅ = S`). -/
theorem couplingCoords_case11_stable (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hc11 : ed.case = StepCase.case11) :
    couplingCoords d (p.extend ed) = couplingCoords d p := by
  -- map: B-globalmove-couplingCoords-case11-stable  ⟨SPECIFY-trivial: case11 arm of couplingCoords = ∅⟩
  sorry

/-- **couplingCoords is monotone under extension** — `couplingCoords d p ⊆ couplingCoords d (p.extend ed)`
(the step arm is `couplingCoords d p ∪ …`). Gives `L_child ⊆ L_parent` — the parent identity restricts to
the child locus for free. SPECIFY-trivial. -/
theorem couplingCoords_mono_extend (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    couplingCoords d p ⊆ couplingCoords d (p.extend ed) := by
  -- map: B-globalmove-couplingCoords-mono-extend  ⟨SPECIFY-trivial: step arm = parent ∪ …⟩
  sorry

/-- **The edge pivot is not an ancestor coupling coordinate (ALL cases)** — the pivot is a diagonal corner
(`canonPivotOf` at case11, `∈ canonCenterOf` diagonal at case12/case2, both via `IsRealBranch`), and
`couplingCoords` are strictly-below-diagonal `belowPivotCol` entries; pnp-verified structurally. Hence
`(couplingClear d (p.extend ed) u) ed.pivot = u ed.pivot` — the `foldB` pivot factor survives the clear. -/
theorem pivot_notMem_couplingCoords_extend (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ed.pivot ∉ couplingCoords d (p.extend ed) := by
  -- map: B-globalmove-pivot-notMem-couplingCoords (pnp: pivot=diagonal corner ∉ strictly-below-diag)
  sorry

/-- **THE LOCUS CONTAINMENT (load-bearing; replaces the false M-level commutation).** `stepMap d ed` sends
`L_child` into `L_parent`: after clearing the child's couplings and applying the step, the ancestor
couplings (`couplingCoords d p`) are still zero — they are spectators of the current step's shear+blow-up.
Stated in directly-usable no-op form: the parent clear fixes the child-cleared, stepped point. pnp-verify. -/
theorem couplingClear_parent_fixes_stepMap_child (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) (u : Fin (flatDim d) → ℝ) :
    couplingClear d p (stepMap d ed (couplingClear d (p.extend ed) u))
      = stepMap d ed (couplingClear d (p.extend ed) u) := by
  -- map: B-globalmove-couplingClear-parent-fixes-stepMap-child (locus containment; ancestor coords spectators)
  sorry

/-- **δ=1 cleared child residual = parent's STRICT TRANSFORM** — the `sourceClearedResid` analogue of
`Case1Wire.foldResid_extend_delta1`. Rides the couplingClear/strict-transform commutation. -/
theorem sourceClearedResid_extend_delta1 (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = true)
    (j : Fin (foldNR d (p.extend ed))) (u : Fin (flatDim d) → ℝ) :
    sourceClearedResid d (p.extend ed) j u
      = sourceClearedResid d p (Fin.cast (foldNR_extend_of_lt d ed hlt) j)
          (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u)) := by
  -- map: B-globalmove-sourceClearedResid-extend-delta1 ((ii) transport; couplingClear/strict-transform comm)
  sorry

/-- **δ=0 cleared child residual = parent's PULLBACK** — the `sourceClearedResid` analogue of
`Case1Wire.foldResid_extend_delta0`. Rides the couplingClear/step-map commutation. -/
theorem sourceClearedResid_extend_delta0 (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = false)
    (j : Fin (foldNR d (p.extend ed))) (u : Fin (flatDim d) → ℝ) :
    sourceClearedResid d (p.extend ed) j u
      = sourceClearedResid d p (Fin.cast (foldNR_extend_of_lt d ed hlt) j) (stepMap d ed u) := by
  -- map: B-globalmove-sourceClearedResid-extend-delta0 ((ii) transport; couplingClear/step-map comm)
  sorry

/-! ### §5 The cleared append (iii) — conjunct A (divisibility ∃q) per-case -/

/-- **Conjunct-A δ=0 PULLBACK branch, cleared** — the `sourceClearedResid` analogue of
`Case1Wire.stepInv_child_delta0`. The child witness is `q' = q ∘ stepMap`. -/
theorem stepInv_child_delta0_cleared (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = false)
    (q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ)
    (hq : StepInv (coreGen d (canonFlatten d)) (clearedFoldG d p) (clearedFoldB d p)
      (sourceClearedResid d p) q (foldRegion d (canonFlatten d) p)) :
    ∃ q' : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d (canonFlatten d)) (clearedFoldG d (p.extend ed)) (clearedFoldB d (p.extend ed))
        (sourceClearedResid d (p.extend ed)) q' (foldRegion d (canonFlatten d) (p.extend ed)) := by
  -- map: B-globalmove-stepInv-child-delta0-cleared (mirror Case1Wire.stepInv_child_delta0 on the cleared trio)
  sorry

/-- **Conjunct-A δ=1 APPEND branch, cleared** — the `sourceClearedResid` analogue of
`Case1Wire.stepInv_child_delta1_append`. Consumes CAPR's `sourceClearedResid_stepMap_eq_pivot_mul`
(the cleared pivot-mul) fed the cleared boost-center Deg1 `hdeg1`; the child witness is `q' = q ∘ stepMap`.
This is where the cleared object earns its keep: the pivot factor divides out because `hdeg1` (property
(D)) holds on `sourceClearedResid` (FALSE on raw `foldResid`). -/
theorem stepInv_child_delta1_append_cleared (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = true)
    (hdeg1 : Deg1SupportedOn (sourceClearedResid d p) ed.center (foldRegion d (canonFlatten d) p))
    (q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ)
    (hq : StepInv (coreGen d (canonFlatten d)) (clearedFoldG d p) (clearedFoldB d p)
      (sourceClearedResid d p) q (foldRegion d (canonFlatten d) p)) :
    ∃ q' : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d (canonFlatten d)) (clearedFoldG d (p.extend ed)) (clearedFoldB d (p.extend ed))
        (sourceClearedResid d (p.extend ed)) q' (foldRegion d (canonFlatten d) (p.extend ed)) := by
  -- map: B-globalmove-stepInv-child-delta1-append-cleared (consumes CAPR sourceClearedResid_stepMap_eq_pivot_mul + hdeg1)
  sorry

/-! ### §6 The cleared cover route (case12) + the cleared conjunct-B step -/

/-- **Cleared cover route (case12/case2 δ=1)** — the `sourceClearedResid` analogue of
`Case1Wire.deg1SupportedOn_center_of_hslot`: from the carried cleared parent slot on `supportAt`, the
cleared parent residual is `Deg1SupportedOn` the ledger center `ed.center`. -/
theorem deg1SupportedOn_center_of_hslot_cleared (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hcase : ed.case = StepCase.case12 ∨ ed.case = StepCase.case2)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d))
    (hslot : ∀ j, Deg1SupportedSlot d (sourceClearedResid d p) j
      (supportAt d p.conState.layer p.conState.cleared) (supportLayerOf p.conState)
      (foldRegion d (canonFlatten d) p)) :
    Deg1SupportedOn (sourceClearedResid d p) ed.center (foldRegion d (canonFlatten d) p) := by
  -- map: B-globalmove-deg1SupportedOn-center-cleared (mirror Case1Wire.deg1SupportedOn_center_of_hslot on cleared)
  sorry

/-- **Cleared conjunct-B step** — the `sourceClearedResid` analogue of
`MonumentAtlas.realBranch_multiAffine_step` (the child `Deg1SupportedSlot` descent on the cleared residual,
from the cleared parent slot + the child branch). -/
theorem realBranch_multiAffine_step_cleared (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (p : TreePath d) (ed : TreeEdge d p) (hlayer : ed.nextState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d))
    (hslot : ∀ j, Deg1SupportedSlot d (sourceClearedResid d p) j
      (supportAt d p.conState.layer p.conState.cleared) (supportLayerOf p.conState)
      (foldRegion d (canonFlatten d) p)) :
    ∀ j, Deg1SupportedSlot d (sourceClearedResid d (p.extend ed)) j
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared)
      (supportLayerOf (p.extend ed).conState) (foldRegion d (canonFlatten d) (p.extend ed)) := by
  -- map: B-globalmove-multiAffine-step-cleared (cleared conjunct-B descent; couplingClear precompose transport)
  sorry

/-! ### §7 The cleared wall — conjunct A dispatch + preservation -/

/-- **Cleared conjunct A (divisibility ∃q) of the wall — dispatched.** δ=0 → `stepInv_child_delta0_cleared`;
δ=1 case11 → `stepInv_child_delta1_append_cleared` fed `realBranch_boostReady_case11'` (the cleared
boost-center Deg1, MergeBoostSplit — its debt is CAPR's `foldResid_case11_mergeBoostSplit_sourceCleared`);
δ=1 case12 → `stepInv_child_delta1_append_cleared` fed `deg1SupportedOn_center_of_hslot_cleared`. -/
theorem case1_conjA_cleared (d : Fin (N + 1) → ℕ) (p : TreePath d) (ed : TreeEdge d p)
    (hcase1 : ed.isCase1) (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt_cleared d (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d (canonFlatten d)) (clearedFoldG d (p.extend ed)) (clearedFoldB d (p.extend ed))
        (sourceClearedResid d (p.extend ed)) q (foldRegion d (canonFlatten d) (p.extend ed)) := by
  -- map: B-globalmove-case1-conjA-cleared (dispatch: delta0 / delta1-case11 boostReady' / delta1-case12 cover)
  sorry

/-- **⟨THE CLEARED WALL⟩ `case1_preserves_cleared`** — the cleared analogue of
`Case1Wire.case1_preserves_stepInv'`. Conjunct A is `case1_conjA_cleared`; conjunct B is
`realBranch_multiAffine_step_cleared`. Produces `FoldStepInvAt_cleared` at the child on the descended
support center. Re-pointed consumer: `CaseStepAssembly.case1_preserves_stepInv''` (per-file go). -/
theorem case1_preserves_cleared (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (p : TreePath d) (ed : TreeEdge d p) (hcase1 : ed.isCase1)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt_cleared d (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    FoldStepInvAt_cleared d
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  -- map: B-globalmove-case1-preserves-cleared (⟨case1_conjA_cleared, realBranch_multiAffine_step_cleared⟩)
  refine ⟨case1_conjA_cleared d p ed hcase1 hlayer hinv hbranch, ?_⟩
  exact realBranch_multiAffine_step_cleared d hpos p ed hlayer hbranch hinv.2

end DLNFibre.DLN.Aoyagi
