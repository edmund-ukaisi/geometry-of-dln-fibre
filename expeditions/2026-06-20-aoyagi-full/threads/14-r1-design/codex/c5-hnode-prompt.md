<task>
You are red-teaming ONE algebraic-geometry claim that decides whether a Lean formalisation effort is
weeks (tractable) or months (open research). DECORRELATED check — I withhold my tentative conclusion.

SETUP. We resolve the RLCT of the loss F(C_1,...,C_L) = ‖C_L · C_{L-1} · … · C_1‖²_Frobenius at the
origin (deepest singular point, where the matrix product is 0). C_s are matrices; layer widths given
by a vector M. A recursion descends node-by-node; at each node it must present the local loss near the
deepest point in a specific "Schur normal form" so a PROVEN squeeze lemma applies.

THE REQUIRED NORMAL FORM ("hnode"). At a node, in suitable local coordinates w split into a regular
part and a block part, the loss must equal, on a neighbourhood of the deepest point:
    flatCore(w) = Σ_j (regular_j)²  +  Σ_{i,j} ( b_i · E_j + SΓ_{i,j} )²
with: (G1) G² := Σ_{i,j} SΓ_{i,j}²  is itself the loss of a SMALLER matrix chain (the "reduced chain",
to be recursed) — i.e. SΓ is a single matrix that equals the product of the remaining factors on the
surviving subspace; (G2) the "pivot column" b satisfies Σ_i b_i² ≤ T² with T → 0 at the deepest point
(b is the blown-up exceptional direction); (G3) the regular_j are a smooth regular sequence (Σ x²
block, contributes a clean ½ each). The squeeze c₁·(Σreg²+G²) ≤ flatCore ≤ c₂·(Σreg²+G²) with
c₁=1/(2(1+T²)), c₂=2+2T² is ALREADY PROVEN for arbitrary b, E, SΓ. So the ONLY open question is whether
the actual node loss can be PUT INTO this form — i.e. the existence of the coordinates exhibiting
flatCore = Σreg² + Σ(b_i E_j + SΓ_ij)² with SΓ a single reduced-chain product.

THE HARD CASE ("C5 / MIXED node"). Most nodes have a clean rank-defect: one factor's rank drops to 0
(or fully couples) — the standard hard-pivot Schur step gives the hnode form (verified for the depth-≤3
case (2,2,2)). The worry is a node with a PARTIAL rank drop: at the active layer s, the incoming prefix
image has rank a, the active factor maps it to rank b with a > b > 0. So b "survivor" dimensions
survive (they pass through several LATER full-rank layers before being killed at a still-later layer),
and a−b "complement" dimensions drop now (coupled to the next factor). Concrete witness:
t = (3,3,2,2,2,0) — at one layer rank drops 3→2 (so a=3, b=2, complement rank 1); the rank-2 survivor
passes through two full-rank layers, killed at the last. This node is NOT a pure-defect node (the
survivor is not killed here), so the question is whether the SINGLE hard-pivot Schur step that clears
the rank-1 complement still yields the hnode form, with SΓ a SINGLE reduced chain (the survivor's
product on the surviving subspace, carried into the recursion), and the pivot column b → 0.

MY OBSERVATIONS (facts, not the conclusion): (i) for a block matrix [[p, row],[col, D]] with p the
pivot (a hard unit after blow-up), the Schur complement is S = D − col·row/p, and ‖[downstream]·[active
factor]‖² groups by columns with EXACT Frobenius orthogonality ‖[X|Y]‖²=‖X‖²+‖Y‖² (no cross terms).
(ii) The survivor passes through FULL-RANK downstream layers ⟹ the downstream map restricted to the
survivor subspace is invertible (a unit gauge). (iii) The partial drop is exactly 1 rank unit here, so
the complement is rank 1 (a single pivot).

THE QUESTION (decide WITNESS vs OBSTRUCTION):
Q1. Does the single hard-pivot Schur step clearing the rank-1 complement at a partial-drop (C5) node
    yield the hnode form flatCore = Σreg² + Σ(b_i E_j + SΓ_ij)² where SΓ is a SINGLE reduced-chain
    product (the survivor's downstream product on the surviving subspace), with b → 0 at the deepest
    point? Or does the survivor's pass-through CONTAMINATE the SΓ block / introduce a SECOND
    independent core / break the single-reduced-chain requirement (G1)?
Q2. Is the "block-column split" (survivor block ⊕ complement block) a basis-choice INSIDE a single
    product DC (so the reduced state is one chain), or does it genuinely produce TWO cores in
    overlapping variables (the shared downstream factors), which would NOT be a single reduced chain
    and would need a product/Fubini treatment the single-hnode form cannot express?
Q3. Does the pivot column b genuinely → 0 at the deepest point for a PARTIAL drop (where part of the
    active factor — the survivor — does NOT vanish at the deepest point)? Or does the survivor's
    non-vanishing keep some "pivot" coordinate bounded away from 0, breaking (G2)?
Q4. NET: can the hnode normal form be produced UNIFORMLY at C5/partial-drop nodes for general M (then
    it is the SAME mechanism as the pure-defect case, formaliser-scale), or is there a genuine
    obstruction at partial-drop nodes that needs a new mechanism (a product/multi-core node type, or a
    geometric argument the single-Schur-step lacks)?
</task>

<output_contract>
Answer Q1–Q4 in order, ≤180 words each. For Q4 end with one line:
VERDICT: WITNESS (hnode uniform at C5, same mechanism) | OBSTRUCTION: <one-sentence precise mechanism gap>.
Mark each claim [FACT] (forced by the stated algebra) or [INFERENCE] (your judgement). Do NOT
rubber-stamp: if the survivor pass-through breaks the single-reduced-chain requirement, say so and give
the minimal counter-structure.
</output_contract>

<grounding_rules>
Reason about matrix-chain products, Schur complements, blow-ups, and Frobenius norms. The load-bearing
distinction: "SΓ is ONE reduced-chain product" (single hnode, recurse on one smaller chain) vs "the node
loss is a SUM of two cores in overlapping variables" (needs a product node the single hnode cannot
express). Keep that distinction explicit. Flag inference vs forced-fact. Do not assume the answer I want.
</grounding_rules>
