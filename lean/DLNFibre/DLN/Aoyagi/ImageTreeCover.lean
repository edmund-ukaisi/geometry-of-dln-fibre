import DLNFibre.DLN.Aoyagi.SurvivorFanCover
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# R2-completion — the UP-TO-NULL branching-tree COVER FOLD

The reroute R2-completion rung: assemble the per-node `SurvivorFanCover` atoms
(`volume_box_diff_charts_eq_zero`) over a branching tree into a whole-tree UP-TO-NULL cover of a
neighbourhood of `0`. This is the "genuine new fold" the R3-derisk flagged: the in-repo precedent
`GeoCoverSpec.flatCube_subset_leafPathImages` folds `buildTree` at a FIXED radius with a FULL cover
(no hole); `LeafCoverTiling.FanTree.covers_subset` carries a GROWING inflated radius over its
branching but is also a FULL cover (block-blow-up baked in). R2 needs the MEASURE version: each node
covers its box only UP-TO-NULL (the survivor-entry `{X=0}` hole), and the whole-tree uncovered set
is the finite union of the pushed-forward per-node holes — still measure-zero.

## Design (Codex-decorrelated, `r2fold-{prompt,answer}.md`)
- A NEUTRAL abstract tree `ImageTree` (nullity lives in the PREDICATE, not the data), NOT an
  extension of the block-blow-up-specific `FanTree`. Node arity is `Fin k` (leanest).
- The set/measure bookkeeping is isolated in ONE generic lemma, `glue_null` (a single node): given
  the node fan covers `A` up-to-null on the FULL domains `B i`, and each chart maps the child's
  domain-residue `B i \ C i` to a null set, then the fan covers `A` up-to-null on the child images
  `C i`. No `C i ⊆ B i`, no injectivity, no measurability needed (outer-measure monotonicity).
- The tree fold `coversUpToNull_volume_diff` is then a routine induction over `glue_null`.
- **Null-transport** (`∀ i N, volume N = 0 → volume (g i '' N) = 0`) is a per-node HYPOTHESIS — the
  weakest compositionally-closed form. For REAL charts it is CHEAP:
  `nullTransport_of_differentiable` discharges it from `Differentiable ℝ g` alone (via Mathlib's
  `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`; the blow-up∘shear charts are
  differentiable). No measure-preservation / det-1 / Lipschitz needed.

## Scope (honest)
- IN: the abstract up-to-null branching cover fold + the one-node gluing lemma + the
  differentiability discharge of null-transport + the connection to the `SurvivorFanCover` atom.
- OUT (R3 / the wire): interpreting the real `buildTree`/`tGeo` into an `ImageTree` (or applying the
  node lemma directly during the `conRel_wf` induction), and discharging the per-node clause with
  the real survivor charts + their `hchart`. This is the cover-side fold engine; the ideal/loss
  lockstep is R3.

## Main results
- `glue_null` — the one-node measure-gluing lemma (all the set/measure bookkeeping).
- `ImageTree`, `leafImages`, `CoversUpToNull` — the abstract tree + its up-to-null cover spec.
- `coversUpToNull_volume_diff` — the fold: `volume (closedBall 0 R \ t.leafImages) = 0`.
- `coversUpToNull_nbhd` — the open-ball (nbhd-of-0) corollary.
- `nullTransport_of_differentiable` — discharge null-transport from differentiability (wire hook).
- `node_clause_of_survivorAtom` — the per-node clause IS the `SurvivorFanCover` atom (the assembly).
- `witness_covers` / `witness_fold` — non-vacuity: a genuine null hole `{0}` propagates via a node.
-/

open MeasureTheory Set Metric

namespace DLNFibre.DLN.Aoyagi.ImageTreeCover

/-! ## The one-node gluing lemma (the isolated set/measure bookkeeping) -/

/-- **One-node measure-gluing.** If the fan `⋃ i, g i '' B i` covers `A` up-to-null (`hnode`) and
each chart sends the domain-residue `B i \ C i` to a null set (`htail`), then the fan
`⋃ i, g i '' C i` covers `A` up-to-null. Pure outer-measure bookkeeping: the uncovered set is
contained in `(A \ ⋃ g i '' B i) ∪ ⋃ i, g i '' (B i \ C i)`, both null. No `C i ⊆ B i`, no
injectivity, no measurability. -/
theorem glue_null {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    {A : Set α} {B C : ι → Set α} {g : ι → α → α}
    (hnode : μ (A \ ⋃ i, g i '' B i) = 0)
    (htail : ∀ i, μ (g i '' (B i \ C i)) = 0) :
    μ (A \ ⋃ i, g i '' C i) = 0 := by
  refine measure_mono_null ?_ (measure_union_null hnode (measure_iUnion_null htail))
  intro x hx
  obtain ⟨hxA, hxC⟩ := hx
  by_cases hB : x ∈ ⋃ i, g i '' B i
  · right
    obtain ⟨i, hi⟩ := mem_iUnion.mp hB
    obtain ⟨y, hyB, hgy⟩ := hi
    have hyC : y ∉ C i := fun h => hxC (mem_iUnion.mpr ⟨i, y, h, hgy⟩)
    exact mem_iUnion.mpr ⟨i, y, ⟨hyB, hyC⟩, hgy⟩
  · exact Or.inl ⟨hxA, hB⟩

/-! ## The abstract up-to-null branching tree -/

variable {D : ℕ}

/-- An abstract **image tree** over `Fin D → ℝ`: a `leaf` carries its source box; a `node` carries a
finite (`Fin k`) family of charts `g` and one child subtree per chart. Nullity lives in the
`CoversUpToNull` predicate, not here. -/
inductive ImageTree (D : ℕ) : Type
  | leaf : Set (Fin D → ℝ) → ImageTree D
  | node : {k : ℕ} → (Fin k → (Fin D → ℝ) → (Fin D → ℝ)) → (Fin k → ImageTree D) → ImageTree D

namespace ImageTree

/-- The accumulated leaf-chart images: a leaf contributes its box; a node fans each chart over its
child's images. -/
def leafImages : ImageTree D → Set (Fin D → ℝ)
  | leaf box => box
  | node g child => ⋃ i, g i '' (child i).leafImages

@[simp] theorem leafImages_leaf (box : Set (Fin D → ℝ)) :
    (ImageTree.leaf box).leafImages = box := rfl

@[simp] theorem leafImages_node {k : ℕ} (g : Fin k → (Fin D → ℝ) → (Fin D → ℝ))
    (child : Fin k → ImageTree D) :
    (ImageTree.node g child).leafImages = ⋃ i, g i '' (child i).leafImages := rfl

/-- **The up-to-null cover spec** (`R`-dependent inflation `f`). A `leaf box` covers
`closedBall 0 R` up-to-null. A `node g child` at radius `R`: (i) each chart is null-preserving
(`htrans`); (ii) the fan covers `closedBall 0 R` up-to-null on the inflated domains
`closedBall 0 (f R)` (the per-node atom); (iii) each child covers the inflated radius `f R`
up-to-null. -/
def CoversUpToNull (f : ℝ → ℝ) : ImageTree D → ℝ → Prop
  | leaf box, R => volume (closedBall 0 R \ box) = 0
  | node g child, R =>
      (∀ i (N : Set (Fin D → ℝ)), volume N = 0 → volume (g i '' N) = 0) ∧
        volume (closedBall (0 : Fin D → ℝ) R \ ⋃ i, g i '' closedBall 0 (f R)) = 0 ∧
        (∀ i, CoversUpToNull f (child i) (f R))

/-- **The up-to-null branching cover fold.** If `CoversUpToNull f t R`, the closed ball of radius
`R` is covered by the tree's leaf-chart images UP-TO-NULL: `volume (closedBall 0 R \ t.leafImages)
= 0`.
Structural induction: the `node` case is exactly `glue_null` (`B i = closedBall 0 (f R)`,
`C i = (child i).leafImages`), the domain-residue `B i \ C i` sent to null by the null-transport
`htrans` applied to the child IH. -/
theorem coversUpToNull_volume_diff {f : ℝ → ℝ} : ∀ (t : ImageTree D) {R : ℝ},
    CoversUpToNull f t R → volume (closedBall (0 : Fin D → ℝ) R \ t.leafImages) = 0 := by
  intro t
  induction t with
  | leaf box => intro R h; exact h
  | node g child ih =>
      intro R h
      obtain ⟨htrans, hnode, hchild⟩ := h
      rw [leafImages_node]
      exact glue_null hnode (fun i => htrans i _ (ih i (hchild i)))

/-- **The open-ball (nbhd-of-0) corollary.** From `CoversUpToNull f t R`, the OPEN ball of radius
`R` is covered up-to-null — the neighbourhood-of-`0` shape the RLCT consumer wants. -/
theorem coversUpToNull_nbhd {f : ℝ → ℝ} (t : ImageTree D) {R : ℝ} (h : CoversUpToNull f t R) :
    volume (ball (0 : Fin D → ℝ) R \ t.leafImages) = 0 :=
  measure_mono_null (Set.diff_subset_diff_left ball_subset_closedBall)
    (coversUpToNull_volume_diff t h)

end ImageTree

/-! ## Discharging null-transport for real (differentiable) charts -/

/-- **Null-transport from differentiability** — the wire hook. A globally differentiable chart maps
null sets to null sets: `Differentiable ℝ g → volume N = 0 → volume (g '' N) = 0`. Via Mathlib's
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (`volume` on `Fin D → ℝ` is an
`IsAddHaarMeasure`). The blow-up∘shear charts are differentiable, so the abstract fold's
null-transport hypothesis is discharged with NO measure-preservation / det-1 / Lipschitz appeal. -/
theorem nullTransport_of_differentiable {g : (Fin D → ℝ) → (Fin D → ℝ)} (hg : Differentiable ℝ g)
    {N : Set (Fin D → ℝ)} (hN : volume N = 0) : volume (g '' N) = 0 := by
  haveI := isAddHaarMeasure_volume_pi (Fin D)
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hg.differentiableOn hN

/-! ## The per-node clause IS the SurvivorFanCover atom (the assembly) -/

open DLNFibre.DLN.Aoyagi.SurvivorFanCover in
/-- **The fold's per-node clause is the `SurvivorFanCover` atom.** With the node's charts the
survivor-entry charts (`g`), the generators `gen`, box `closedBall 0 R`, and per-chart domain the
inflated ball `closedBall 0 fR`, the per-node up-to-null clause
`volume (closedBall 0 R \ ⋃ a, g a '' closedBall 0 fR) = 0` is EXACTLY
`SurvivorFanCover.volume_box_diff_charts_eq_zero`. This is the assembly link: the tree fold consumes
one atom per node. -/
theorem node_clause_of_survivorAtom {k : ℕ} [Nonempty (Fin k)] {R fR : ℝ} (hR : 1 ≤ R)
    (gen : Fin k → (Fin D → ℝ) → ℝ) (g : Fin k → (Fin D → ℝ) → (Fin D → ℝ))
    (hchart : ∀ a, survivorRegion R gen a ∩ closedBall 0 R ⊆ g a '' closedBall 0 fR)
    (hnull : volume (commonZero gen) = 0) :
    volume (closedBall (0 : Fin D → ℝ) R \ ⋃ a, g a '' closedBall 0 fR) = 0 :=
  volume_box_diff_charts_eq_zero hR gen (closedBall 0 R) g (fun _ => closedBall 0 fR) hchart hnull

/-! ## Non-vacuity: a genuine null hole `{0}` propagates through a node -/

/-- A one-node witness tree (arity 1, identity chart) whose single child is a leaf whose box is the
unit ball MINUS the origin — a genuine up-to-null leaf (hole `{0}`). -/
def witnessTree : ImageTree 2 :=
  ImageTree.node (k := 1) (fun _ => id) (fun _ => ImageTree.leaf (closedBall 0 1 \ {0}))

/-- The witness tree satisfies `CoversUpToNull (fun _ => 1) · 1`: the identity chart is
null-preserving, the node clause is a FULL self-cover of the unit ball (`id` images), and the child
leaf covers the unit ball up-to the null hole `{0}`. Genuinely exercises the node fold + a real hole
(unlike a full-cover witness). -/
theorem witness_covers : ImageTree.CoversUpToNull (fun _ => (1 : ℝ)) witnessTree 1 := by
  have hsingle : volume ({0} : Set (Fin 2 → ℝ)) = 0 := measure_singleton 0
  refine ⟨fun _ N hN => by rwa [Set.image_id], ?_, fun _ => ?_⟩
  · -- node clause: id images of the unit ball self-cover the unit ball
    have hU : (⋃ (_ : Fin 1), (id : (Fin 2 → ℝ) → _) '' closedBall 0 ((fun _ => (1:ℝ)) 1))
        = closedBall (0 : Fin 2 → ℝ) 1 := by
      rw [Set.iUnion_const, Set.image_id]
    rw [hU, Set.diff_self, measure_empty]
  · -- child leaf covers the unit ball up-to `{0}`
    change volume (closedBall (0 : Fin 2 → ℝ) 1 \ (closedBall 0 1 \ {0})) = 0
    refine measure_mono_null ?_ hsingle
    intro x hx
    by_contra hx0
    exact hx.2 ⟨hx.1, hx0⟩

/-- **Non-vacuity (fold fires with a real hole).** The fold applied to the witness tree yields
`volume (closedBall 0 1 \ witnessTree.leafImages) = 0` — the whole-tree cover misses exactly the
codim-2 null hole `{0}`, which the fold proves null. -/
theorem witness_fold :
    volume (closedBall (0 : Fin 2 → ℝ) 1 \ witnessTree.leafImages) = 0 :=
  ImageTree.coversUpToNull_volume_diff witnessTree witness_covers

-- Forced axiom gate: the fold + gluing lemma + wire hook + assembly link + witnesses rest only on
-- `[propext, Classical.choice, Quot.sound]`. Force-elaborates (no stale-olean masking).
#assert_banked_clean_batch [glue_null, ImageTree.coversUpToNull_volume_diff,
  ImageTree.coversUpToNull_nbhd, nullTransport_of_differentiable, node_clause_of_survivorAtom,
  witness_covers, witness_fold]

end DLNFibre.DLN.Aoyagi.ImageTreeCover
