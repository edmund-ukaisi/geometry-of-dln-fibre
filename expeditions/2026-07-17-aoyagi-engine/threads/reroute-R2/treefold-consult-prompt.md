<task>
Lean 4 + Mathlib v4.29 proof DESIGN review (do NOT write the full proof; pin the motive + descent
skeleton + 2-3 bookkeeping lemmas). We are building a radius-parameterized cover fold over a
well-founded recursion, marrying two banked halves.

BANKED PRECEDENT (fixed radius): 
  flatCube_subset_leafPathImages : ∀ (s : ConState L) (acc : Params M → Params M),
    cubeBox (flatDim M) 1 ⊆ leafPathImages (tGeo acc (buildTree M (conOracle M) s))
proved by  `induction s using (conRel_wf M).induction`, `cases conOracle M s`:
  - terminal: leaf srcBox = the fixed cube.
  - step node children: `node_selfCover` (the node's pivot charts self-cover the FIXED cube) +
    `fannedEdges_covers` + IH `ih c.child c.hdesc acc`. Radius is FIXED at 1 throughout; no shear
    inflation. `leafPathImages (branch n edges) = ⋃ e ∈ edges, e.subst.localSub '' leafPathImages e.child`.

BANKED PER-NODE CLAUSE (radius, no branching):
  bornSiblings_union_covers (Z hZ c hkeep dom) (hR : 0<R)
    (hshearcov : closedBall 0 (max R 1) ⊆ c.shear '' dom) :
    ball 0 R ⊆ ⋃ p:{p//p∈Z}, (bornSiblings Z c hkeep p.1 p.2).stepMap '' dom
  where stepMap p = blockBlowupMap Z p ∘ c.shear. Also banked: FanTree.Covers f t R (an inductive
  cover predicate over a LINEAR step-list with per-node R-dependent inflation f=r↦r+C·r², max R 1
  floor) + covers_subset : Covers f t R → closedBall 0 R ⊆ t.leafImages.

GOAL (marry them): 
  ∀ (R:ℝ) (acc), closedBall 0 R ⊆ leafImages (tGeo acc (buildTree M (conOracle M) s))
where the covered radius GROWS down the real BRANCHING tree: at a node, cover the parent box
closedBall 0 R by the children's images, each child covering up to the INFLATED radius f (max R 1) by
IH; global C* = max width dominates every node's local C. Design constraints (HARD): fixed-full-space
Params M (no dimension drop), leaf-indexed family.

QUESTIONS:
(1) MOTIVE shape for the conRel_wf induction: universally quantify R INSIDE the motive
    (`∀ R acc, closedBall 0 R ⊆ leafImages …`) so the IH is instantiable at f(max R 1)? Or thread R
    as an accumulator? Which avoids the WellFounded.fix motive pitfalls?
(2) PER-NODE DESCENT: the node clause needs closedBall 0 R ⊆ ⋃ children, stepMap '' (child leafImages),
    and child leafImages ⊇ closedBall 0 (f(max R 1)) from IH-at-f(max R 1), then bornSiblings_union_covers
    lifts. Is there an order-of-quantifier / monotonicity pitfall — leafImages is a FIXED set per
    subtree, but the RADIUS it covers depends on R via the IH? How to thread "the child covers the
    inflated radius" cleanly (image-monotonicity `A ⊆ B → g '' A ⊆ g '' B`)?
(3) dom threading: bornSiblings_union_covers needs closedBall 0 (max R 1) ⊆ c.shear '' dom. In the
    fold, what is dom — the child's leafImages? So the hypothesis becomes closedBall 0 (max R 1) ⊆
    c.shear '' (child leafImages), and c.shear '' (child leafImages) relates to the child's covered
    radius how? Is the right decomposition (a) shear covers the inflated box [banked
    blockShear_covers_of_norm_bound], (b) child covers the shear-preimage box [IH], composed?
</task>

<output_contract>
Four short sections: (1) MOTIVE — the exact `∀ R acc, …` shape + why (WF-fix pitfall). (2) DESCENT
SKELETON — the per-node case, 4-6 bullet steps, naming the image-monotonicity + IH-instantiation
points. (3) BOOKKEEPING LEMMAS — the 2-3 small lemmas to state first (image-mono, f-inflation
monotone, the shear∘child dom composition). (4) FRICTION — the top 2-3 Lean pitfalls (motive shape,
dom/leafImages threading, f-monotonicity) + the cheapest guard for each. Terse. Flag inference vs
fact.
</output_contract>

<grounding_rules>
You are reviewing a DESIGN, not verifying a build. Mark any claim about specific Mathlib lemma names
as INFERENCE (I cannot verify names for you). Focus on the proof ARCHITECTURE (motive, descent,
threading) which is toolchain-independent. Do not invent our lemma names; refer to the ones I gave.
</grounding_rules>
