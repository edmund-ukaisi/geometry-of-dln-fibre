import DLNFibre.DLN.RLCT.Engine.EngineDefs
import DLNFibre.DLN.RLCT.Engine.PivotCover

/-!
# `DLNFibre.DLN.RLCT.Engine.PivotCoverFold` — T3 rung 2 (THE FOLD): SCOPING SKELETON

**Blueprint spine: statements are forecasts; this is a STATEMENT-FIRST scoping pass — bodies are
`sorry`, held for the combined (rung-1 fidelity + rung-2 statement) review. No proof grind yet.**

Rung 1 (`PivotCover.lean`) proved the per-blow-up atom: the `d` max-modulus pivot charts of one
origin blow-up cover the cube. Rung 2 folds that atom up the resolution tree to `ChartBridge`'s
tree-level image-cover clause (`EngineDefs.lean:76`):

    ∃ U open, {A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ⊆ ⋃ l ∈ leaves t, chartMap '' srcBox.

## The fold structure (at altitude)

`leafPathImages t` = the union of the own-rooted leaf-chart images of a subtree (`leafPaths id t`).
It satisfies the clean recursion (`leafPathImages_branch`)

    leafPathImages (branch n edges) = ⋃ e ∈ edges, e.subst.localSub '' leafPathImages e.child,

because `leafPaths (acc ∘ s) c` prepends `s` to every own-rooted composite of `c`. So a downstairs
cover folds by tree induction: if each child covers its region (IH) and the node's edges' images of
those regions cover a neighbourhood of the node's region (`ownCovers_branch`'s `hnode`), the node
covers its region. `hnode` at a genuine blow-up node reduces to the rung-1 atom
(`node_pivotCover_of_atom`, the flat-coordinate embedding of `iUnion_pivotChart_image_eq_cubeBox`).

## ⚠ INTERFACE SURFACE (controller specific #3 — STOP-AND-SURFACE, do not bake silently)

`ownCovers_branch`'s `hnode` demands the node's edges realize a pivot family whose images COVER a
neighbourhood of the center — i.e. **edge pivot-completeness** (the FULL residual-`d` family, per
`cert-atlas-probe` Verdict 1(b): a corner-only edge set has the explicit gap). §2's `StepEmit`
(`t2-buildtree-design.md §1`) leaves `hlive : 0 < edges.length ∨ True` LOOSE — it does NOT force
this. And §1's "one Case-1 blow-up emits a 1(1) + a 1(2) edge" (two charts) is not obviously the
`d`-pivot cover. **OPEN interface question (surfaced to controller/architect):** is the full pivot
family (i) emitted as `d` pivot-chart edges per blow-up node by `buildTree`, or (ii) realized across
the tree's branching + proven via `CompChainInv` (`EngineConstruction.lean:286`,
invariant→principalization, fork 12(c))? The statements below carry `hnode` EXPLICITLY so the answer
is visible, not assumed.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The own-rooted leaf-chart image set** of a subtree: the union of `φ '' l.srcBox` over the
leaf/composite pairs of `leafPaths id t` (`acc = id`, so `φ` is the SUBTREE-root→leaf fold). By the
`ChartBridge` coherence clause, on the FULL tree this equals `⋃ l ∈ leaves t, l.chartMap '' srcBox`
(each leaf's stored `chartMap` is its `leafPaths id` composite). -/
def leafPathImages (t : ResolutionTree M) : Set (Params M) :=
  ⋃ p ∈ ResolutionTree.leafPaths (id : Params M → Params M) t, p.2 '' p.1.srcBox

/-- **The fold identity** (the recursion the tree induction rides on): a branch's own-rooted images
are the union, over its edges, of the edge substitution applied to the child's own-rooted images.
Structural: `leafPaths (acc ∘ s) c` prepends `s` to `c`'s own-rooted composites. -/
theorem leafPathImages_branch (n : StepData M) (edges : List (Edge M)) :
    leafPathImages (ResolutionTree.branch n edges)
      = ⋃ e ∈ edges, e.subst.localSub '' leafPathImages e.child := by
  sorry

/-- **A subtree COVERS a downstairs set `V`** if its own-rooted leaf images contain an open
neighbourhood of `V`. The tree-level image-cover clause of `ChartBridge` is exactly
`OwnCovers (resolutionOf M) {zero-locus ∩ unit box}` transported by coherence. -/
def OwnCovers (t : ResolutionTree M) (V : Set (Params M)) : Prop :=
  ∃ U : Set (Params M), IsOpen U ∧ V ⊆ U ∧ U ⊆ leafPathImages t

/-- **The FOLD (inductive step).** If every child covers its assigned region (`hchild`, the IH) and
the node's edges' images of those regions cover a neighbourhood of `V` (`hnode`, the per-node
pivot-completeness — the interface surface above; discharged at a blow-up node by the rung-1 atom),
then the node covers `V`. The witnessing open is `hnode`'s (child regions sit inside the children's
own images by `hchild`, which sit inside the branch's own images by `leafPathImages_branch`). -/
theorem ownCovers_branch {n : StepData M} {edges : List (Edge M)} {V : Set (Params M)}
    {childRegion : Edge M → Set (Params M)}
    (hchild : ∀ e ∈ edges, OwnCovers e.child (childRegion e))
    (hnode : ∃ U : Set (Params M), IsOpen U ∧ V ⊆ U ∧
      U ⊆ ⋃ e ∈ edges, e.subst.localSub '' childRegion e) :
    OwnCovers (ResolutionTree.branch n edges) V := by
  sorry

/-- **The per-node atom bridge** (rung-2's real content + the interface surface): at a blow-up node
whose edges are the pivot charts of a center that is a coordinate block of dimension `d`, `hnode`
holds — it is the rung-1 atom `iUnion_pivotChart_image_eq_cubeBox` embedded into the flat
coordinates (`Fin (flatDim M)`) via the center's coordinate indices, untouched coordinates passing
through. The `pivotComplete` hypothesis names exactly what `buildTree` must supply (the ⚠ surface).
Case-1's center `{d_ij = 0, u_{s,k} = 0}` (pp.15-16) and Case-2's residual block (pp.19-20,
running-min FIX-A labels) differ only in WHICH coordinates form the center; the atom is uniform. -/
theorem node_pivotCover_of_atom {n : StepData M} {edges : List (Edge M)} {V : Set (Params M)}
    {childRegion : Edge M → Set (Params M)}
    -- PLACEHOLDER for the edge-pivot-completeness contract (§2 must force it; see ⚠ surface):
    (pivotComplete : True) :
    ∃ U : Set (Params M), IsOpen U ∧ V ⊆ U ∧
        U ⊆ ⋃ e ∈ edges, e.subst.localSub '' childRegion e := by
  sorry

/-- **The headline** (rung-2 target): the `ChartBridge` image-cover clause follows from
`OwnCovers (resolutionOf M)` of the zero-locus-in-the-unit-box, via coherence
(`leaf.chartMap = leafPaths id` composite) turning `leafPathImages` into `⋃ l ∈ leaves, chartMap ''
srcBox`. This is the clause `coverage_theorem` (`EngineObligations.lean:65`) owes. -/
theorem chartBridge_imageCover_of_ownCovers (t : ResolutionTree M)
    (hcoh : ∀ p ∈ ResolutionTree.leafPaths (id : Params M → Params M) t, p.1.chartMap = p.2)
    (hcov : OwnCovers t {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0}) :
    ∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ l ∈ ResolutionTree.leaves t, l.chartMap '' l.srcBox := by
  sorry

end DLNFibre.DLN.RLCT.Engine
