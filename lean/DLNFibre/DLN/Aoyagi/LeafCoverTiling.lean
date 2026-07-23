import DLNFibre.Core.Aoyagi.BlockBlowupCover
import DLNFibre.Core.Aoyagi.PathAtoms

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

/-! ## The abstract fan-cover tree (per-node shears + `R`-dependent box inflation; MILESTONE 2)

The pnp-fan cover fold (`fan-design-certificate.md` §2.3–2.4) as an abstract, monument-free
recursion
over the FULL pivot fan. A `node` carries a NONEMPTY center `S`, a per-pivot shear `σ p`, and one
child subtree per pivot (`child p` for every `p ∈ S` — the full fan, elder ruling (A): pivots range
over ALL of `S`, NOT the col-pinned ledger). Rollovers are `pass`; a `leaf` carries its source box
(the atlas `dom`, compact).

The per-node step is `blockBlowupMap S p ∘ σ p` (block blow-up OUTERMOST, shear inner) — the
monument's `stepMap`. The shear (case-1(2)/case-2 `edgeShear`) is a bijection that can INFLATE a
box;
the fold absorbs it by an **`R`-dependent** inflation `f : ℝ → ℝ` (`Covers f t R` below), NOT a
constant factor: the monument's `canonNormalizationOf` is QUADRATIC (`σ⁻¹ ~ r + C·r²` on a
radius-`r`
box), so a constant multiplier `K` is UNDISCHARGEABLE at depth ≥ 2 (`K ≥ 1 + K^ℓ` has no solution) —
rev-L7cover's finding. A super-geometric `f` (e.g. `r ↦ r·(1+r)`) closes each per-node shear clause,
and a finite-depth tree gives finite (large) leaf boxes `f^[depth] 1` = cert §2.4's `R·(1+R)^m`. The
`max R 1` floor is the atom's (the ratio slots need radius `≥ 1`), so the strategy is DUAL to §2.4's
small-`ρ`: keep the covered ball at radius 1 and INFLATE the leaf boxes to `f^[depth] 1` (the atlas
`dom` sized accordingly at the wire), rather than shrink `ρ`. The concrete `f` for
`canonNormalizationOf`, the fan-completeness (`buildTree` realises every pivot), and the `#86(B)`
col→full σ-bridge are discharged at the WIRE (controller-owned; this module cannot import
`MonumentAtlas`, which imports it). -/

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

/-- **The fold cover condition** (`R`-dependent inflation `f`, target radius `R`). At a `leaf box`
the box covers `closedBall 0 R`; at a `pass` the child covers `R`; at a `node S σ` each pivot
shear
maps an `f (max R 1)`-box over the source box `closedBall 0 (max R 1)` (the LOCAL shear fact — `σ⁻¹`
maps the source box into the `f`-inflated box), AND each child covers the inflated radius
`f (max R 1)`. A super-geometric `f` (e.g. `r ↦ r·(1+r)`) absorbs the monument's QUADRATIC shear
over
finite depth (a constant multiplier cannot — rev-L7cover); NON-vacuous (each clause is a local
containment on explicit boxes, never the global cover). -/
def Covers (f : ℝ → ℝ) : FanTree D → ℝ → Prop
  | .leaf box, R => closedBall 0 R ⊆ box
  | .pass child, R => Covers f child R
  | .node S _ σ child, R =>
      (∀ p ∈ S, closedBall 0 (max R 1) ⊆ (σ p) '' closedBall 0 (f (max R 1))) ∧
        (∀ p ∈ S, Covers f (child p) (f (max R 1)))

/-- **The abstract fan cover (with shears).** If `Covers f t R` holds, the closed ball of radius `R`
is covered by the tree's leaf-chart images — the pnp-fan tree fold with `R`-dependent box inflation,
by structural induction: each `node` is discharged by the closed block-atom `(Q)` at radius `R`, the
local shear fact, and the child IH at the inflated radius `f (max R 1)`. -/
theorem covers_subset {f : ℝ → ℝ} : ∀ (t : FanTree D) {R : ℝ}, Covers f t R →
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
`Covers f t 1` (the controller's wire discharges it: leaf boxes `≥ f^[depth] 1`, the shear facts
from `canonNormalizationOf`'s quadratic bound against the `f`-box, the fan-completeness from
`buildTree`). -/
theorem exists_ball_subset_leafImages {f : ℝ → ℝ} (t : FanTree D) (h : Covers f t 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : Fin D → ℝ) ρ ⊆ t.leafImages :=
  ⟨1, one_pos, Metric.ball_subset_closedBall.trans (covers_subset t h)⟩

/-- **Non-vacuity witness** — a one-node fan tree (singleton center, identity shear, unit-box leaf)
satisfies `Covers id · 1` (the linear/no-inflation instance `f = id`), so `covers_subset` /
`exists_ball_subset_leafImages` fire non-trivially on a genuine fanned node (not a bare leaf). -/
theorem covers_one_node (p : Fin D) :
    Covers id (FanTree.node {p} ⟨p, Finset.mem_singleton_self p⟩ (fun _ ↦ id)
      (fun _ ↦ FanTree.leaf (closedBall 0 1))) 1 :=
  ⟨fun _ _ ↦ by simp [Set.image_id], fun _ _ ↦ by simp [Covers]⟩

/-! ### Acceptance witness (rev-L7cover): a genuine QUADRATIC shear, nested DEPTH ≥ 2, `|S| = 2`,
closes under the `R`-dependent inflation `f = r ↦ r + r²`. This exercises the exact case that BROKE
the constant-`K` form (the old `covers_one_node`, `σ = id`, did not reach it). -/

/-- A concrete genuine quadratic Schur shear on `Fin 3`: identity except coord `2 ↦ v₂ − v₀·v₁`.
Unipotent (det 1); its inverse adds back the quadratic `x₀·x₁`. -/
def qshear (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun i ↦ if i = 2 then v 2 - v 0 * v 1 else v i

/-- The inverse of `qshear` (`x₂ ↦ x₂ + x₀·x₁`). -/
def qinv (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun i ↦ if i = 2 then x 2 + x 0 * x 1 else x i

theorem qshear_qinv (x : Fin 3 → ℝ) : qshear (qinv x) = x := by
  funext i; fin_cases i <;> simp [qshear, qinv]

/-- **The load-bearing discharge**: for the quadratic shear `qshear`, `σ⁻¹` maps the radius-`r` box
into the radius-`(r + r²)` box, so `closedBall 0 r ⊆ qshear '' closedBall 0 (r + r²)` at EVERY `r`.
This is what a constant `K` cannot do — the `r²` term forces the `R`-dependent inflation. -/
theorem qshear_covers {r : ℝ} (hr : 0 ≤ r) :
    closedBall (0 : Fin 3 → ℝ) r ⊆ qshear '' closedBall 0 (r + r ^ 2) := by
  have hrr : (0 : ℝ) ≤ r + r ^ 2 := by positivity
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr] at hx
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2
  rw [Real.norm_eq_abs] at h0 h1 h2
  refine ⟨qinv x, ?_, qshear_qinv x⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hrr]
  intro i
  rw [Real.norm_eq_abs]
  obtain ⟨h0l, h0r⟩ := abs_le.mp h0
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  by_cases hi : i = 2
  · subst hi
    change |x 2 + x 0 * x 1| ≤ r + r ^ 2
    have p1 : (0 : ℝ) ≤ (r - x 0) * (r + x 1) := mul_nonneg (by linarith) (by linarith)
    have p2 : (0 : ℝ) ≤ (r + x 0) * (r - x 1) := mul_nonneg (by linarith) (by linarith)
    have p3 : (0 : ℝ) ≤ (r - x 0) * (r - x 1) := mul_nonneg (by linarith) (by linarith)
    have p4 : (0 : ℝ) ≤ (r + x 0) * (r + x 1) := mul_nonneg (by linarith) (by linarith)
    have hub : x 0 * x 1 ≤ r ^ 2 := by nlinarith [p1, p2]
    have hlb : -(r ^ 2) ≤ x 0 * x 1 := by nlinarith [p3, p4]
    rw [abs_le]
    exact ⟨by linarith [h2l, hlb], by linarith [h2r, hub]⟩
  · simp only [qinv, if_neg hi]
    have hxi : |x i| ≤ r := by rw [← Real.norm_eq_abs]; exact hx i
    nlinarith [sq_nonneg r]

/-- A depth-2 fan tree with `|S| = 2` centers and the genuine quadratic `qshear` at BOTH levels. -/
def qtree : FanTree 3 :=
  FanTree.node {0, 1} ⟨0, by decide⟩ (fun _ ↦ qshear)
    (fun _ ↦ FanTree.node {0, 1} ⟨0, by decide⟩ (fun _ ↦ qshear)
      (fun _ ↦ FanTree.leaf (closedBall 0 6)))

/-- **Acceptance witness (rev-L7cover)** — the depth-2, `|S| = 2`, genuine-quadratic-shear tree
satisfies `Covers (r ↦ r + r²) · 1`: the `R`-dependent inflation discharges the quadratic shear
nested twice (`f 1 = 2` at the root shear-box, `f 2 = 6` at the child, leaf box `closedBall 0 6`),
which the constant-`K` form provably could not. -/
theorem covers_qtree : Covers (fun r ↦ r + r ^ 2) qtree 1 :=
  ⟨fun _ _ ↦ qshear_covers (zero_le_one.trans (le_max_right _ 1)),
    fun _ _ ↦ ⟨fun _ _ ↦ qshear_covers (zero_le_one.trans (le_max_right _ 1)),
      fun _ _ ↦ Metric.closedBall_subset_closedBall (by norm_num)⟩⟩

/-! ### Regression witness (rev-L7cover): the EXACT old counterexample shear `σ(x,y) = (x, y + x²)`
— `blockShear cexPhi`, `cexPhi u = (0, (u 0)²)`, Codex's value-leaf counterexample from the
fan-design cert — CLOSES the cover under `f = r ↦ r + r²`, depth 2, `|S| = 2`. Banked as a
regression against the exact `σ` that broke the value leaves under a frozen shear (the cover, unlike
the value leaves, transfers: a bijective shear omits no target point). Uses the REAL `blockShear`,
complementing the bespoke `qshear` above. -/

/-- The counterexample displacement `φ u = (0, (u 0)²)`, so `blockShear cexPhi` is Codex's shear
`σ(x,y) = (x, y + x²)`. -/
def cexPhi (u : Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦ if i = 1 then (u 0) ^ 2 else 0

/-- The counterexample shear closes the cover under `f = r ↦ r + r²` (its inverse
`x ↦ (x₀, x₁ − x₀²)` maps the radius-`r` box into the radius-`(r + r²)` box). -/
theorem cexShear_covers {r : ℝ} (hr : 0 ≤ r) :
    closedBall (0 : Fin 2 → ℝ) r ⊆ blockShear cexPhi '' closedBall 0 (r + r ^ 2) := by
  have hrr : (0 : ℝ) ≤ r + r ^ 2 := by positivity
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr] at hx
  have h0 := hx 0; have h1 := hx 1
  rw [Real.norm_eq_abs] at h0 h1
  obtain ⟨h0l, h0r⟩ := abs_le.mp h0
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  refine ⟨blockShearInv cexPhi x, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hrr]
    intro i
    rw [Real.norm_eq_abs]
    by_cases hi : i = 1
    · subst hi
      change |x 1 - (x 0) ^ 2| ≤ r + r ^ 2
      have hsq : (x 0) ^ 2 ≤ r ^ 2 := by nlinarith [h0l, h0r]
      rw [abs_le]
      exact ⟨by nlinarith [h1l, sq_nonneg (x 0)], by nlinarith [h1r, hsq]⟩
    · have hval : blockShearInv cexPhi x i = x i := by simp [blockShearInv, cexPhi, if_neg hi]
      rw [hval]
      have hxi : |x i| ≤ r := by rw [← Real.norm_eq_abs]; exact hx i
      nlinarith [sq_nonneg r]
  · funext i; fin_cases i <;> simp [blockShear, blockShearInv, cexPhi]

/-- A depth-2 fan tree with `|S| = 2` and the exact counterexample shear at BOTH levels. -/
def cexTree : FanTree 2 :=
  FanTree.node {0, 1} ⟨0, by decide⟩ (fun _ ↦ blockShear cexPhi)
    (fun _ ↦ FanTree.node {0, 1} ⟨0, by decide⟩ (fun _ ↦ blockShear cexPhi)
      (fun _ ↦ FanTree.leaf (closedBall 0 6)))

/-- **Regression witness (rev-L7cover)** — the counterexample-shear tree closes under
`f = r ↦ r + r²`: `Covers (r ↦ r + r²) cexTree 1`, the exact `σ(x,y)=(x,y+x²)` nested twice. -/
theorem covers_cexTree : Covers (fun r ↦ r + r ^ 2) cexTree 1 :=
  ⟨fun _ _ ↦ cexShear_covers (zero_le_one.trans (le_max_right _ 1)),
    fun _ _ ↦ ⟨fun _ _ ↦ cexShear_covers (zero_le_one.trans (le_max_right _ 1)),
      fun _ _ ↦ Metric.closedBall_subset_closedBall (by norm_num)⟩⟩

end FanTree

end DLNFibre.DLN.Aoyagi.LeafCoverTiling
