import DLNFibre.Core.Aoyagi.BlockBlowupCover

/-!
# `DLNFibre.DLN.Aoyagi.LeafCoverTiling` — the general-`d` fan cover-tiling (L7, ruling-indep. core)

The abstract, monument-free cover engine for `leafPath_compactCover` (L7, `MonumentAtlas.lean`).
Per the elder's L7 SPECIFY ruling (A) — prompted by the seat-L7cover mini-restate's `(2,2,2)` escape
`ε·e_{(0,0,1)}`, which escapes every #87 col-pinned root chart yet IS covered by the FULL fan
(pnp-fan §4): the cover is the ABSTRACT FULL-FAN cover — pivots over ALL of a center `S`, NOT
the col-pinned ledger. The col-pin is for the leaf-invariant (ledger), never the cover. Two pieces
are CONTROLLER-owned (detail-at-scale, riding `buildTree`+`#86(B)`-gauge, not a frontier):
fan-completeness (that the atlas realises every admissible pivot — discharged from `buildTree`) and
the col-pinned→full-fan σ-bridge (`#86(B)` column-orbit transport). This module gives the
engine; the controller instantiates it and discharges those two at the wire (it cannot import
`MonumentAtlas`, which imports this — hence the abstraction).

The pnp-fan mechanism (`threads/L7/fan-design-certificate.md` §2, mirroring the engine's sorry-free
`GeoCoverSpec.node_selfCover → fannedEdges_covers → flatCube_subset_leafPathImages`):
* per-node ATOM = seat-Q's sorry-free
  `Core.Aoyagi.BlockBlowupCover.ball_subset_iUnion_blockBlowup_image_radius`
  (`ball 0 R ⊆ ⋃ p ∈ S, blockBlowupMap S p '' closedBall 0 (max R 1)`, argmax-over-`S` routing);
* the tree FOLD lifts that atom one node at a time — the inductive STEP is
  `ball_subset_iUnion_blockBlowup_comp` below: if, for each pivot `p ∈ S`, the continuing charts
  tagged `p` cover the source box, then the composed charts `blockBlowupMap S (pv i) ∘ g i` cover
  `ball 0 R`.

The step is stated SHEAR-FREE: the block blow-up is applied outermost within a step, so the pivot
fan does the covering; the per-step shear, when present (case-1(2)/case-2), is a global bijection
absorbed into the child region by an `R·(1+R)^m` box inflation — a separate brick held with the
top-statement. Both forks (A: abstract full-fan; B: col-pinned) consume this same step; whether its
hypothesis `hcov` can be met is exactly the fork question (under B the col-pin drops the pivots
`hcov` needs).
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi.LeafCoverTiling

variable {D : ℕ}

/-- **One-step block-blow-up FAN-LIFT** — the inductive step of the pnp-fan cover fold, shear-free.

Given a nonempty center `S ⊆ Fin D` and, for each pivot `p ∈ S`, a family of continuing charts
`{(g i, A i) : pv i = p}` whose images cover the source box `closedBall 0 (max R 1)`, the images of
the composed charts `blockBlowupMap S (pv i) ∘ g i` cover `ball 0 R`. The routing is the argmax over
`S` (seat-Q's atom `ball_subset_iUnion_blockBlowup_image_radius`): a target `x ∈ ball 0 R` lifts to
`x = blockBlowupMap S p w` with `w` in the box and `p ∈ S` the maximiser; `hcov p` then realises `w`
by a continuing chart tagged `p`, and composing recovers `x`. -/
theorem ball_subset_iUnion_blockBlowup_comp
    {S : Finset (Fin D)} (hS : S.Nonempty) {R : ℝ} (hR : 0 < R)
    {ι : Type*} (g : ι → ((Fin D → ℝ) → (Fin D → ℝ))) (A : ι → Set (Fin D → ℝ))
    (pv : ι → Fin D)
    (hcov : ∀ p ∈ S,
      closedBall (0 : Fin D → ℝ) (max R 1) ⊆ ⋃ i ∈ {i | pv i = p}, (g i) '' (A i)) :
    ball (0 : Fin D → ℝ) R ⊆ ⋃ i, (blockBlowupMap S (pv i) ∘ g i) '' (A i) := by
  intro x hx
  -- the argmax atom: `x = blockBlowupMap S p w` for some pivot `p ∈ S`, `w` in the source box
  obtain ⟨p, hpS, w, hw, hwx⟩ :=
    Set.mem_iUnion₂.mp (ball_subset_iUnion_blockBlowup_image_radius hS hR hx)
  -- realise `w` by a continuing chart tagged `p` (the fan-completeness hypothesis `hcov`)
  obtain ⟨i, hi, z, hz, hgz⟩ := Set.mem_iUnion₂.mp (hcov p hpS hw)
  -- compose: `(blockBlowupMap S (pv i) ∘ g i) z = blockBlowupMap S p w = x`
  simp only [Set.mem_setOf_eq] at hi
  rw [Set.mem_iUnion]
  refine ⟨i, z, hz, ?_⟩
  simp only [Function.comp_apply]
  rw [hgz, hi, hwx]

/-! ## The closed-ball block-atom (the fold's self-cover form) -/

/-- **The closed-ball block-atom `(Q)`** — the closed variant of seat-Q's
`ball_subset_iUnion_blockBlowup_image_radius`, needed for the fold's SELF-cover (the source box a
node hands its children is CLOSED). Same argmax-over-`S` routing; `x ∈ closedBall 0 R` lifts with
the pivot `p = argmax_{q ∈ S} |x q|`, `w_p = x_p`, `w_q = x_q / x_p` (`≤ 1` by maximality),
spectators passed through. -/
theorem closedBall_subset_iUnion_blockBlowup_image_radius {S : Finset (Fin D)} (hS : S.Nonempty)
    {R : ℝ} (hR : 0 ≤ R) :
    closedBall (0 : Fin D → ℝ) R ⊆
      ⋃ p ∈ S, (blockBlowupMap S p) '' (closedBall 0 (max R 1)) := by
  have h0 : (0 : ℝ) ≤ max R 1 := le_trans zero_le_one (le_max_right R 1)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR] at hx
  obtain ⟨p, hpS, hp⟩ := Finset.exists_max_image S (fun j ↦ |x j|) hS
  have hxpR : |x p| ≤ max R 1 := by
    have h := hx p; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left R 1)
  rw [Set.mem_iUnion₂]
  refine ⟨p, hpS, ?_⟩
  by_cases hxp : x p = 0
  · -- max over `S` is `0` ⟹ every center coordinate is `0`; spectators pass through unchanged
    have hxj0 : ∀ q ∈ S, x q = 0 := fun q hq ↦ by
      have := hp q hq; rw [hxp, abs_zero] at this; exact abs_nonpos_iff.mp this
    refine ⟨fun j ↦ if j ∈ S then 0 else x j, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg h0]
      intro j
      rw [Real.norm_eq_abs]
      by_cases hjS : j ∈ S
      · simp only [if_pos hjS, abs_zero]; exact h0
      · simp only [if_neg hjS]
        have h := hx j; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left R 1)
    · funext j
      by_cases hj : j = p
      · subst hj; simp [blockBlowupMap, hpS, hxp]
      · by_cases hjS : j ∈ S
        · simp only [blockBlowupMap, if_neg hj, if_pos hjS, if_pos hpS, mul_zero]
          exact (hxj0 j hjS).symm
        · simp [blockBlowupMap, hj, hjS]
  · -- max over `S` is nonzero: the standard argmax lift, ratios `≤ 1` by maximality
    refine ⟨fun j ↦ if j = p then x p else if j ∈ S then x j / x p else x j, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg h0]
      intro j
      rw [Real.norm_eq_abs]
      by_cases hj : j = p
      · rw [hj]; simpa using hxpR
      · by_cases hjS : j ∈ S
        · simp only [if_neg hj, if_pos hjS, abs_div]
          exact le_trans ((div_le_one (abs_pos.mpr hxp)).mpr (hp j hjS)) (le_max_right R 1)
        · simp only [if_neg hj, if_neg hjS]
          have h := hx j; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left R 1)
    · funext j
      by_cases hj : j = p
      · subst hj; simp [blockBlowupMap]
      · by_cases hjS : j ∈ S
        · simp [blockBlowupMap, hj, hjS, mul_div_cancel₀, hxp]
        · simp [blockBlowupMap, hj, hjS]

/-- The unit-radius closed self-cover:
`closedBall 0 1 ⊆ ⋃ p ∈ S, blockBlowupMap S p '' closedBall 0 1` (`max 1 1 = 1`). Fold's per-node
self-cover — each pivot chart's source box is again `closedBall 0 1`, so the block blow-up is a
SELF-cover of the unit cube (ratios `≤ 1`, no inflation — the shear-free case). -/
theorem closedBall_one_subset_iUnion_blockBlowup_image {S : Finset (Fin D)} (hS : S.Nonempty) :
    closedBall (0 : Fin D → ℝ) 1 ⊆ ⋃ p ∈ S, (blockBlowupMap S p) '' (closedBall 0 1) := by
  have h := closedBall_subset_iUnion_blockBlowup_image_radius hS (zero_le_one)
  rwa [max_self] at h

/-! ## The abstract fan-cover tree (shear-free core; MILESTONE 1)

The pnp-fan cover fold (`fan-design-certificate.md` §2.3) as an abstract, monument-free recursion
over the FULL pivot fan. A `node` carries a NONEMPTY center `S` and one child subtree per pivot
(`child p` for every `p ∈ S` — the full fan, matching the elder's (A) ruling: pivots range over ALL
of `S`, NOT the col-pinned ledger). Rollovers are `pass` (identity passthrough). SHEAR-FREE: the
per-step shear (case-1(2)/case-2), when present, is absorbed by an `R·(1+R)^m` box inflation into
the child region — a separate brick, held with the top-statement (elder L7 SPECIFY). The controller
instantiates this tree from `buildTree` and maps its leaf-charts onto the atlas (fan-completeness
discharge + the `#86(B)` col→full σ-bridge, both controller-owned). -/

/-- An abstract **fan-cover tree** over `Fin D → ℝ`: `leaf` (source box = the closed unit cube),
`pass` (rollover / identity passthrough, single child), or `node S hS child` (a full pivot fan over
a nonempty center `S`, one child per pivot). -/
inductive FanTree (D : ℕ) : Type
  | leaf : FanTree D
  | pass : FanTree D → FanTree D
  | node : (S : Finset (Fin D)) → S.Nonempty → (Fin D → FanTree D) → FanTree D

namespace FanTree

/-- The accumulated union of leaf-chart images from a node, root-outermost. A `leaf` contributes its
source box `closedBall 0 1`; a `pass` passes its child through; a `node S` fans the block blow-up
over `S`. Equals `⋃ leaf-paths, (root-outermost composition) '' (leaf box)`. -/
def leafImages : FanTree D → Set (Fin D → ℝ)
  | .leaf => closedBall 0 1
  | .pass child => child.leafImages
  | .node S _ child => ⋃ p ∈ S, (blockBlowupMap S p) '' (child p).leafImages

@[simp] theorem leafImages_leaf : (FanTree.leaf : FanTree D).leafImages = closedBall 0 1 := rfl

@[simp] theorem leafImages_pass (child : FanTree D) :
    (FanTree.pass child).leafImages = child.leafImages := rfl

@[simp] theorem leafImages_node (S : Finset (Fin D)) (hS : S.Nonempty) (child : Fin D → FanTree D) :
    (FanTree.node S hS child).leafImages = ⋃ p ∈ S, (blockBlowupMap S p) '' (child p).leafImages :=
  rfl

/-- **The abstract fan cover (shear-free).** The closed unit cube is covered by the leaf images
of any fan-cover tree — the pnp-fan tree fold, by structural induction on the tree, each `node`
discharged by the closed block-atom at radius 1 (`closedBall_one_subset_iUnion_blockBlowup_image`)
composed with the child IH. -/
theorem closedBall_one_subset_leafImages (t : FanTree D) :
    closedBall (0 : Fin D → ℝ) 1 ⊆ t.leafImages := by
  induction t with
  | leaf => simp
  | pass child ih => simpa using ih
  | node S hS child ih =>
      rw [leafImages_node]
      intro x hx
      obtain ⟨p, hpS, w, hw, hwx⟩ :=
        Set.mem_iUnion₂.mp (closedBall_one_subset_iUnion_blockBlowup_image hS hx)
      exact Set.mem_iUnion₂.mpr ⟨p, hpS, w, ih p hw, hwx⟩

/-- **The open-ball corollary** (`∃ ρ > 0`) — the shape `leafPath_compactCover` consumes. -/
theorem exists_ball_subset_leafImages (t : FanTree D) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : Fin D → ℝ) ρ ⊆ t.leafImages :=
  ⟨1, one_pos, Metric.ball_subset_closedBall.trans t.closedBall_one_subset_leafImages⟩

end FanTree

end DLNFibre.DLN.Aoyagi.LeafCoverTiling
