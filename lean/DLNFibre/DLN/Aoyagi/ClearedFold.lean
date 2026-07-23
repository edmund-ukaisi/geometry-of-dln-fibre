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

/-! ### §4 The cleared transports (ii) — the couplingClear/(strict-transform, step-map) commutations

The child↔parent commutation (frame §6 shape (S2), pnp-verified at every node). These are the
load-bearing NEW content of the append re-point; the case11 form needs `ed.pivot ∉ couplingCoords d p`
(the reused-divisor birth corner is a diagonal accumulated pivot, disjoint from the strictly-below-diagonal
ancestor coupling coords), the case12/case2 form additionally tracks the freshly-added `belowPivotCol`.
OWNERSHIP FLAG (SPECIFY): `couplingCoords`/`accumulatedPivots` are CAPR's primitives; whether the
`pivot ∉ couplingCoords` disjointness + the case12/case2 commutation are mine to prove or CAPR-provided is
a SPECIFY question (see the message). -/

/-- **couplingCoords stability under a case11 extension** (controller SPECIFY note; the transports lean
on it) — a case11 step adds no `belowPivotCol` (it is a MERGE into an existing exceptional, not a fresh
clear), so `couplingCoords d (p.extend ed) = couplingCoords d p`. Hence at case11 the child clear map
equals the parent's, which is what makes the case11 step-map commutation clean. SPECIFY-trivial (the
`couplingCoords` step arm's case11 match is `∅`, and `S ∪ ∅ = S`). -/
theorem couplingCoords_case11_stable (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hc11 : ed.case = StepCase.case11) :
    couplingCoords d (p.extend ed) = couplingCoords d p := by
  -- map: B-globalmove-couplingCoords-case11-stable  ⟨SPECIFY-trivial: case11 arm of couplingCoords = ∅⟩
  sorry

/-- **The couplingClear/step-map commutation** — `stepMap d ed ∘ couplingClear d (p.extend ed) =
couplingClear d p ∘ stepMap d ed`. Frame §6 (S2). -/
theorem couplingClear_stepMap_comm (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    (stepMap d ed) ∘ (couplingClear d (p.extend ed)) = (couplingClear d p) ∘ (stepMap d ed) := by
  -- map: B-globalmove-couplingClear-stepMap-comm (frame §6 S2; case11 needs pivot∉couplingCoords)
  sorry

/-- **`clearedFoldG` one-step law** — `clearedFoldG (p.extend ed) = clearedFoldG p ∘ stepMap d ed` (rides
the step-map commutation). -/
theorem clearedFoldG_extend_eq (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    clearedFoldG d (p.extend ed) = clearedFoldG d p ∘ stepMap d ed := by
  -- map: B-globalmove-clearedFoldG-extend (via couplingClear_stepMap_comm + foldG one-step)
  sorry

/-- **`clearedFoldB` one-step ratio** — `clearedFoldB (p.extend ed) u = u_pivot^δ · clearedFoldB p
(stepMap d ed u)`, `δ = edgeδ d p`. The pivot factor is `u ed.pivot` (NOT `(couplingClear u) ed.pivot`)
because the pivot is disjoint from the coupling coords. The clean-monomial fact (frame §6). -/
theorem clearedFoldB_extend_eq (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (u : Fin (flatDim d) → ℝ) :
    clearedFoldB d (p.extend ed) u
      = (u ed.pivot) ^ (if edgeδ d p then 1 else 0) * clearedFoldB d p (stepMap d ed u) := by
  -- map: B-globalmove-clearedFoldB-extend (foldB one-step + couplingClear_stepMap_comm + pivot∉couplingCoords)
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
