import DLNFibre.Core.Aoyagi.BlockBlowupCover

/-!
# `DLNFibre.DLN.Aoyagi.LeafCoverTiling` — the general-`d` fan cover-tiling (L7, ruling-indep. core)

Staged scaffolding for `leafPath_compactCover` (L7, `MonumentAtlas.lean`). The gated TOP-statement
(the full-center fan vs the #87 col-pinned atlas; fan-completeness as a hypothesis vs a
`FoldRealizes` def-edit) is HELD pending the elder ruling on the `(2,2,2)` col-pin coverage escape
(seat-L7cover
mini-restate: `ε·e_{(0,0,1)}` escapes every col-pinned root chart, matching pnp-fan §4's own witness
under the *full* fan). What is banked here is the FORK-INDEPENDENT core the pnp-fan option-(b) cover
fold rests on under EITHER fork.

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

end DLNFibre.DLN.Aoyagi.LeafCoverTiling
