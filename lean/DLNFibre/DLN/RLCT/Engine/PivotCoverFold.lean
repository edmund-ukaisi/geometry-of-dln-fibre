import DLNFibre.DLN.RLCT.Engine.EngineDefs
import DLNFibre.DLN.RLCT.Engine.PivotCover

/-!
# `DLNFibre.DLN.RLCT.Engine.PivotCoverFold` — T3 rung 2 (THE FOLD): SCOPING SKELETON

**Blueprint spine: statement-first pass, since PROVEN — all four fold theorems carry proofs
(the combined rung-1 fidelity + rung-2 statement review passed; see cert-cov-rungs12).**

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

mutual
/-- **The own-rooted leaf-chart image set** of a subtree, by structural recursion (mirroring
`ResolutionTree.edgesLeaves`): a leaf contributes `l.srcBox` (own image, `acc = id`); a branch is
the union over its edges of the edge substitution applied to the child's image set. Equals
`⋃ p ∈ leafPaths id t, p.2 '' p.1.srcBox` (a HELD lemma, via the accumulator factoring), which under
`ChartBridge` coherence is `⋃ l ∈ leaves t, chartMap '' srcBox`. Recursing directly (not through
`leafPaths`) makes the fold identity below `image_comp`-free. -/
def leafPathImages : ResolutionTree M → Set (Params M)
  | .leaf l => l.srcBox
  | .branch _ edges => edgesImages edges
/-- Companion of `leafPathImages` over an edge list (mutual structural recursion). -/
def edgesImages : List (Edge M) → Set (Params M)
  | [] => ∅
  | .mk _ s c :: es => s.localSub '' leafPathImages c ∪ edgesImages es
end

/-- **The fold identity** (the recursion the tree induction rides on): a branch's own-rooted images
are the union, over its edges, of the edge substitution applied to the child's own-rooted images.
`image_comp`-free — the recursion is definitional; only the list-`biUnion` cons is set logic. -/
theorem leafPathImages_branch (n : StepData M) (edges : List (Edge M)) :
    leafPathImages (ResolutionTree.branch n edges)
      = ⋃ e ∈ edges, e.subst.localSub '' leafPathImages e.child := by
  simp only [leafPathImages]
  induction edges with
  | nil => simp [edgesImages]
  | cons e es ih =>
      obtain ⟨c, s, ch⟩ := e
      simp only [edgesImages, ih]
      ext y
      simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons, exists_prop]
      constructor
      · rintro (hy | ⟨x, hx, hy⟩)
        · exact ⟨Edge.mk c s ch, Or.inl rfl, hy⟩
        · exact ⟨x, Or.inr hx, hy⟩
      · rintro ⟨x, (rfl | hx), hy⟩
        · exact Or.inl hy
        · exact Or.inr ⟨x, hx, hy⟩

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
  obtain ⟨U, hUopen, hVU, hUcov⟩ := hnode
  refine ⟨U, hUopen, hVU, hUcov.trans ?_⟩
  rw [leafPathImages_branch]
  refine Set.iUnion₂_mono (fun e he => Set.image_mono ?_)
  obtain ⟨Ue, _, hReg, hUe⟩ := hchild e he
  exact hReg.trans hUe

/-! ## The `leafPaths` connection (the headline bridge)

`leafPathImages` was defined by direct recursion; to feed `ChartBridge`'s image-cover clause (stated
over `leaves`/`chartMap`) we bridge it back to the `leafPaths id` composites via the accumulator
factoring `imgAcc` and the first-projection identity `leafPaths_mapFst`. Both are mutual inductions
over the tree/edge-list, mirroring `ResolutionTree.edgesLeaves`. -/

mutual
/-- **Accumulator factoring**: the union of the `leafPaths acc` composite-images is `acc` applied to
the own-rooted image set. Mutual with `imgEdgesAcc`. -/
theorem imgAcc (acc : Params M → Params M) :
    ∀ t : ResolutionTree M,
      (⋃ p ∈ ResolutionTree.leafPaths acc t, p.2 '' p.1.srcBox) = acc '' leafPathImages t
  | .leaf l => by
      simp only [ResolutionTree.leafPaths, leafPathImages, List.mem_singleton,
        Set.iUnion_iUnion_eq_left]
  | .branch _ edges => by
      simp only [ResolutionTree.leafPaths, leafPathImages]
      exact imgEdgesAcc acc edges
/-- Companion of `imgAcc` over an edge list. -/
theorem imgEdgesAcc (acc : Params M → Params M) :
    ∀ edges : List (Edge M),
      (⋃ p ∈ ResolutionTree.edgesLeafPaths acc edges, p.2 '' p.1.srcBox) = acc '' edgesImages edges
  | [] => by simp [ResolutionTree.edgesLeafPaths, edgesImages]
  | .mk _ s c :: es => by
      simp only [ResolutionTree.edgesLeafPaths, edgesImages, List.mem_append, Set.iUnion_or,
        Set.iUnion_union_distrib]
      rw [imgAcc (acc ∘ s.localSub) c, imgEdgesAcc acc es]
      have hcomp : (acc ∘ s.localSub) '' leafPathImages c
          = acc '' (s.localSub '' leafPathImages c) :=
        Set.image_comp acc s.localSub (leafPathImages c)
      rw [hcomp, Set.image_union]
end

/-- `leafPathImages t` is the union of the `leafPaths id` composite-images (`imgAcc` at `acc = id`).
The bridge from the recursive def back to the `leafPaths`-composite form coherence reads. -/
theorem leafPathImages_eq_biUnion_leafPaths (t : ResolutionTree M) :
    leafPathImages t = ⋃ p ∈ ResolutionTree.leafPaths (id : Params M → Params M) t,
      p.2 '' p.1.srcBox := by
  simpa only [Set.image_id] using (imgAcc (id : Params M → Params M) t).symm

mutual
/-- **First-projection identity**: the leaves of `leafPaths acc t` (any `acc`) are `leaves t`.
Mutual with `edgesLeafPaths_mapFst`. -/
theorem leafPaths_mapFst (acc : Params M → Params M) :
    ∀ t : ResolutionTree M,
      (ResolutionTree.leafPaths acc t).map Prod.fst = ResolutionTree.leaves t
  | .leaf _ => by simp [ResolutionTree.leafPaths, ResolutionTree.leaves]
  | .branch _ edges => by
      simp only [ResolutionTree.leafPaths, ResolutionTree.leaves]
      exact edgesLeafPaths_mapFst acc edges
/-- Companion of `leafPaths_mapFst` over an edge list. -/
theorem edgesLeafPaths_mapFst (acc : Params M → Params M) :
    ∀ edges : List (Edge M),
      (ResolutionTree.edgesLeafPaths acc edges).map Prod.fst = ResolutionTree.edgesLeaves edges
  | [] => by simp [ResolutionTree.edgesLeafPaths, ResolutionTree.edgesLeaves]
  | .mk _ s c :: es => by
      simp only [ResolutionTree.edgesLeafPaths, ResolutionTree.edgesLeaves, List.map_append]
      rw [leafPaths_mapFst (acc ∘ s.localSub) c, edgesLeafPaths_mapFst acc es]
end

/-- **The per-node atom bridge** (rung-2's real content, PROVEN; (a)-generalized, cert-cov-rungs12).
At a blow-up node whose edges realize the FULL pivot family of a codimension-`d` coordinate center,
`hnode` holds — the rung-1 atom `iUnion_pivotChart_image_eq_cubeBox` transported through the
construction's coordinate split `q : Params M ≃ₜ (Fin d → ℝ) × E` (center coords × spectators). The
contract (= the architect's `StepEmit` `pivotComplete` amendment):
* `pivotOf` tags each edge with its pivot; `hbij` = FULL family (every `i : Fin d` realized) — the
  load-bearing (a)-vs-(b) content: emitting fewer than `d` pivots leaves the corner gap
  (`corner_chart_not_cover`, cert-atlas-probe 1(b)); the ATLAS COUNTS are blind to it (symmetric
  quotient) — the page (center codim) + the corner ¬-theorem are the discriminators;
* `hloc` = each edge's `localSub` is the `q`-conjugated `pivotChart`; `hdom` = its `childRegion` is
  the `q`-preimage of the max-modulus sub-cube; `hV` = `V` in the open center-slab (needs `0 < R`).
Case-1's center `{d_ij=0, u_{s,k}=0}` (p.16, `d = J₁·(M^{(S+1)}−J)+1`) and Case-2's residual block
(p.19, `d = (M(S)−J)·(M^{(S+1)}−J)`) differ only in WHICH coords form the center; the atom is
uniform (`page-pin-centers.md`). Element-chase via the atom; `q`-independent of the tree. -/
theorem node_pivotCover_of_atom {edges : List (Edge M)} {V : Set (Params M)}
    {childRegion : Edge M → Set (Params M)} {d : ℕ} {E : Type*} [TopologicalSpace E]
    (hd : 0 < d) {R : ℝ} (hR : 0 < R) (q : Params M ≃ₜ (Fin d → ℝ) × E)
    (pivotOf : Edge M → Fin d)
    (hbij : ∀ i : Fin d, ∃ e ∈ edges, pivotOf e = i)
    (hloc : ∀ e ∈ edges, ∀ w : Params M,
      e.subst.localSub w = q.symm (Prod.map (pivotChart (pivotOf e)) id (q w)))
    (hdom : ∀ e ∈ edges, childRegion e = q ⁻¹' (pivotChartDom (pivotOf e) R ×ˢ Set.univ))
    (hV : V ⊆ q ⁻¹' ((Set.univ.pi fun _ => Set.Ioo (-R) R) ×ˢ Set.univ)) :
    ∃ U : Set (Params M), IsOpen U ∧ V ⊆ U ∧
        U ⊆ ⋃ e ∈ edges, e.subst.localSub '' childRegion e := by
  refine ⟨q ⁻¹' ((Set.univ.pi fun _ => Set.Ioo (-R) R) ×ˢ Set.univ), ?_, hV, ?_⟩
  · exact q.isOpen_preimage.mpr
      ((isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).prod isOpen_univ)
  · intro w hw
    rw [Set.mem_preimage, Set.mem_prod] at hw
    have hcube : (q w).1 ∈ cubeBox d R := by
      rw [cubeBox, Set.mem_pi]
      intro k _
      have hk := hw.1 k (Set.mem_univ k)
      rw [Set.mem_Ioo] at hk
      exact Set.mem_Icc.mpr ⟨le_of_lt hk.1, le_of_lt hk.2⟩
    rw [← iUnion_pivotChart_image_eq_cubeBox hd (le_of_lt hR), Set.mem_iUnion] at hcube
    obtain ⟨i, u, hu, hpc⟩ := hcube
    obtain ⟨e, he, hei⟩ := hbij i
    rw [Set.mem_iUnion₂]
    refine ⟨e, he, q.symm (u, (q w).2), ?_, ?_⟩
    · rw [hdom e he, Set.mem_preimage, Homeomorph.apply_symm_apply, Set.mem_prod]
      exact ⟨by rw [hei]; exact hu, Set.mem_univ _⟩
    · rw [hloc e he, Homeomorph.apply_symm_apply, hei]
      simp only [Prod.map_apply, id_eq, hpc]
      rw [← Prod.mk.eta (p := q w), Homeomorph.symm_apply_apply]

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
  obtain ⟨U, hUopen, hVU, hUsub⟩ := hcov
  refine ⟨U, hUopen, hVU, hUsub.trans ?_⟩
  rw [leafPathImages_eq_biUnion_leafPaths]
  intro y hy
  simp only [Set.mem_iUnion, exists_prop] at hy ⊢
  obtain ⟨p, hp, hy⟩ := hy
  refine ⟨p.1, ?_, ?_⟩
  · rw [← leafPaths_mapFst (id : Params M → Params M) t]
    exact List.mem_map_of_mem hp
  · rwa [hcoh p hp]

end DLNFibre.DLN.RLCT.Engine
