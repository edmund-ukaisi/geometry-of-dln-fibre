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

/-! ## The abstract fan-cover tree (with per-node shears + box inflation; MILESTONE 2)

The pnp-fan cover fold (`fan-design-certificate.md` §2.3–2.4) as an abstract, monument-free
recursion
over the FULL pivot fan. A `node` carries a NONEMPTY center `S`, a per-pivot shear `σ p`, and one
child subtree per pivot (`child p` for every `p ∈ S` — the full fan, matching elder ruling (A):
pivots range over ALL of `S`, NOT the col-pinned ledger). Rollovers are `pass` (identity
passthrough). A `leaf` carries its source box (the atlas `dom`, compact).

The per-node step is `blockBlowupMap S p ∘ σ p` (block blow-up OUTERMOST; the shear inner) — exactly
the monument's `stepMap`. The shear (case-1(2)/case-2 `edgeShear`) is a global bijection that can
INFLATE a box by a bounded factor; the fold absorbs it by the `R·(1+R)^m` box inflation
(`fan-design-certificate.md` §2.4): the cover radius stays `≥ 1` (the atom's `max R 1` source),
grows by the inflation factor `K` per shear level, so the LEAVES cover a `K^depth` box and the ROOT
covers the unit ball. That inflation is threaded by `Covers K t R` below — the LOCAL per-node shear
fact `closedBall 0 (max R 1) ⊆ σ p '' closedBall 0 (K·max R 1)` (the shear maps a `K·`-box over the
source box, i.e. `σ⁻¹` is `K`-bounded there) plus the child covering the inflated radius. The
concrete `K` for the monument's `canonNormalizationOf`, the fan-completeness (`buildTree` realises
every pivot), and the `#86(B)` col→full σ-bridge are all discharged at the WIRE (controller-owned;
this module cannot import `MonumentAtlas`, which imports it). -/

/-- An abstract **fan-cover tree** over `Fin D → ℝ`: `leaf box` (a compact source box), `pass`
(rollover / identity passthrough, single child), or `node S hS σ child` (a full pivot fan over a
nonempty center `S`, with per-pivot shear `σ p` and one child per pivot). -/
inductive FanTree (D : ℕ) : Type
  | leaf : Set (Fin D → ℝ) → FanTree D
  | pass : FanTree D → FanTree D
  | node : (S : Finset (Fin D)) → S.Nonempty →
      (Fin D → (Fin D → ℝ) → (Fin D → ℝ)) → (Fin D → FanTree D) → FanTree D

namespace FanTree

/-- The accumulated union of leaf-chart images from a node, root-outermost. A `leaf box` contributes
`box`; a `pass` passes its child through; a `node S σ` fans the step `blockBlowupMap S p ∘ σ p` over
`S`. Equals `⋃ leaf-paths, (root-outermost composition) '' (leaf box)`. -/
def leafImages : FanTree D → Set (Fin D → ℝ)
  | .leaf box => box
  | .pass child => child.leafImages
  | .node S _ σ child => ⋃ p ∈ S, (blockBlowupMap S p ∘ σ p) '' (child p).leafImages

@[simp] theorem leafImages_leaf (box : Set (Fin D → ℝ)) :
    (FanTree.leaf box).leafImages = box := rfl

@[simp] theorem leafImages_pass (child : FanTree D) :
    (FanTree.pass child).leafImages = child.leafImages := rfl

@[simp] theorem leafImages_node (S : Finset (Fin D)) (hS : S.Nonempty)
    (σ : Fin D → (Fin D → ℝ) → (Fin D → ℝ)) (child : Fin D → FanTree D) :
    (FanTree.node S hS σ child).leafImages =
      ⋃ p ∈ S, (blockBlowupMap S p ∘ σ p) '' (child p).leafImages := rfl

/-- **The fold cover condition** (inflation factor `K`, target radius `R`). At a `leaf box` the box
covers `closedBall 0 R`; at a `pass` the child covers `R`; at a `node S σ` each pivot's shear maps a
`K·(max R 1)`-box over the source box `closedBall 0 (max R 1)` (the LOCAL shear fact — `σ⁻¹` is
`K`-bounded there), AND each child covers the inflated radius `K·(max R 1)`. Threads the `R·(1+R)^m`
inflation structurally; NON-vacuous (each clause is a local containment, never the global cover). -/
def Covers (K : ℝ) : FanTree D → ℝ → Prop
  | .leaf box, R => closedBall 0 R ⊆ box
  | .pass child, R => Covers K child R
  | .node S _ σ child, R =>
      (∀ p ∈ S, closedBall 0 (max R 1) ⊆ (σ p) '' closedBall 0 (K * max R 1)) ∧
        (∀ p ∈ S, Covers K (child p) (K * max R 1))

/-- **The abstract fan cover (with shears).** If `Covers K t R` holds, the closed ball of radius `R`
is covered by the tree's leaf-chart images — the pnp-fan tree fold with box inflation, by structural
induction: each `node` is discharged by the closed block-atom `(Q)` at radius `R`, the local shear
fact, and the child IH at the inflated radius. -/
theorem covers_subset {K : ℝ} : ∀ (t : FanTree D) {R : ℝ}, Covers K t R →
    closedBall (0 : Fin D → ℝ) R ⊆ t.leafImages := by
  intro t
  induction t with
  | leaf box => intro R h; exact h
  | pass child ih => intro R h; exact ih h
  | node S hS σ child ih =>
      intro R h
      obtain ⟨hshear, hchild⟩ := h
      by_cases hR : 0 ≤ R
      · rw [leafImages_node]
        intro x hx
        obtain ⟨p, hpS, w, hw, hwx⟩ :=
          Set.mem_iUnion₂.mp (closedBall_subset_iUnion_blockBlowup_image_radius hS hR hx)
        obtain ⟨z, hz, hzw⟩ := hshear p hpS hw
        refine Set.mem_iUnion₂.mpr ⟨p, hpS, z, ih p (hchild p hpS) hz, ?_⟩
        simp only [Function.comp_apply]
        rw [hzw]; exact hwx
      · rw [Metric.closedBall_eq_empty.mpr (not_le.mp hR)]; exact Set.empty_subset _

/-- **The open-ball corollary** (`∃ ρ > 0`) — the shape `leafPath_compactCover` consumes. From
`Covers K t 1` (the controller's wire discharges it: leaf boxes `≥ K^depth`, the shear facts from
`canonNormalizationOf`, the fan-completeness from `buildTree`). -/
theorem exists_ball_subset_leafImages {K : ℝ} (t : FanTree D) (h : Covers K t 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : Fin D → ℝ) ρ ⊆ t.leafImages :=
  ⟨1, one_pos, Metric.ball_subset_closedBall.trans (covers_subset t h)⟩

/-- **Non-vacuity witness** — a one-node fan tree (singleton center, identity shear, unit-box leaf)
satisfies `Covers 1 · 1`, so `covers_subset` / `exists_ball_subset_leafImages` fire non-trivially on
a genuine fanned node (not just a bare leaf). -/
theorem covers_one_node (p : Fin D) :
    Covers 1 (FanTree.node {p} ⟨p, Finset.mem_singleton_self p⟩ (fun _ ↦ id)
      (fun _ ↦ FanTree.leaf (closedBall 0 1))) 1 :=
  ⟨fun _ _ ↦ by simp [Set.image_id], fun _ _ ↦ by simp [Covers]⟩

end FanTree

end DLNFibre.DLN.Aoyagi.LeafCoverTiling
