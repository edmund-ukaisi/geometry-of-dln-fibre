<task>
Lean 4 + Mathlib (v4.29) formalisation design review. I am building the "R2-completion" rung of a
resolution-of-singularities cover fold. I have a per-NODE atom already proven; I need the whole-TREE
fold. Validate the design of a new abstract measure-theoretic fold before I write it.

CONTEXT (all real, in-repo):
- Space is `Fin D → ℝ` with `MeasureTheory.volume` (the pi Lebesgue measure). `Metric.closedBall`.
- Per-node atom ALREADY PROVEN (SurvivorFanCover): for a finite family of "charts"
  `chart : ι → (Fin D → ℝ) → (Fin D → ℝ)` and domains, if each chart covers its "survivor region"
  within a box, then `volume (box \ ⋃ a, chart a '' dom a) = 0` — an UP-TO-NULL per-node cover
  (uncovered ⊆ a measure-zero hole {X=0}).
- Existing FULL-cover branching fold (flatCube, over a resolution `buildTree` via WellFounded.fix):
  gives `closedBall 0 1 ⊆ leafPathImages tree` (NO hole). Existing abstract full-cover fold FanTree
  with radius inflation `f`: `Covers f t R → closedBall 0 R ⊆ t.leafImages`.
- Shear box-inflation brick: `blockShear_covers_of_norm_bound` gives
  `closedBall 0 r ⊆ blockShear φ '' closedBall 0 (r + r^2)` (a quadratic-inflation radius `f r = r+r^2`).

GOAL: an ABSTRACT branching-tree fold producing an UP-TO-NULL whole-tree cover:
`volume (closedBall 0 R \ leafImages t) = 0`, assembling the per-node up-to-null atoms.

PROPOSED DESIGN (please red-team):

  inductive NullTree (D : ℕ) : Type
    | leaf : Set (Fin D → ℝ) → NullTree D
    | node : {k : ℕ} → (Fin k → (Fin D → ℝ) → (Fin D → ℝ)) → (Fin k → NullTree D) → NullTree D

  def leafImages : NullTree D → Set (Fin D → ℝ)
    | leaf box => box
    | node g child => ⋃ i, g i '' (child i).leafImages

  def CoversUpToNull (f : ℝ → ℝ) : NullTree D → ℝ → Prop
    | leaf box, R => volume (closedBall 0 R \ box) = 0
    | node g child, R =>
        (∀ i (N : Set (Fin D → ℝ)), volume N = 0 → volume (g i '' N) = 0) ∧          -- null-transport
        (volume (closedBall 0 R \ ⋃ i, g i '' closedBall 0 (f R)) = 0) ∧             -- per-node up-to-null
        (∀ i, CoversUpToNull f (child i) (f R))                                       -- children at inflated radius

  theorem coversUpToNull_volume_diff (f) : ∀ t R,
      CoversUpToNull f t R → volume (closedBall 0 R \ (leafImages t)) = 0

Node-case proof sketch (Dom := closedBall 0 (f R)):
  closedBall 0 R \ ⋃ i, g i '' (child i).leafImages
    ⊆ (closedBall 0 R \ ⋃ i, g i '' Dom) ∪ ⋃ i, g i '' (Dom \ (child i).leafImages)
  first term null by the per-node clause; each `g i '' (Dom \ child.leafImages)` null by null-transport
  applied to the IH `volume (Dom \ child_i.leafImages) = 0`; finite union of null is null.
  The set inclusion: x in LHS; if x ∉ ⋃ g i '' Dom → first term; else x = g i y, y ∈ Dom, and since
  x ∉ g i '' child.leafImages we get y ∉ child.leafImages, so y ∈ Dom \ child.leafImages.
</task>

<output_contract>
Answer in these sections, terse:
1. VERDICT: is the design sound and the node-case inclusion correct? (yes/no + the one flaw if any)
2. MEASURE PITFALLS: any Mathlib v4.29 gotcha with `measure_iUnion_null` / `measure_mono_null` /
   `volume (g '' N)` for a finite `Fin k` union, or the `closedBall 0 R \ ...` bookkeeping. Name the
   exact lemmas you'd use.
3. NULL-TRANSPORT: is taking `∀ i N, volume N = 0 → volume (g i '' N) = 0` as a hypothesis the right
   call (vs deriving it)? For the real charts `blockShear φ` (a C¹/Lipschitz diffeo, det 1,
   measure-preserving), what is the CLEANEST Mathlib route to discharge it later — and is there a
   trap (e.g. Lipschitz-image-of-null needs the map defined on all of ℝ^D, or a σ-finiteness/
   measurability condition)?
4. DESIGN: reuse FanTree (block-blowup baked into node) or a NEW inductive as proposed? Any better
   shape for the node arity (Fin k vs a Finset vs Fintype ι)? Should the leaf base case be
   `volume (closedBall 0 R \ box) = 0` (up-to-null) or `closedBall 0 R ⊆ box` (full)?
5. SCOPE: is this the right MINIMAL first brick for "assemble per-node up-to-null atoms over a
   branching tree", or is there a smaller/cleaner honest first target?
</output_contract>

<grounding_rules>
Flag any claim about a specific Mathlib lemma NAME as "inference — verify" unless you are certain it
exists at v4.29. Distinguish "this will typecheck" (design) from "this exact lemma exists" (API).
</grounding_rules>
