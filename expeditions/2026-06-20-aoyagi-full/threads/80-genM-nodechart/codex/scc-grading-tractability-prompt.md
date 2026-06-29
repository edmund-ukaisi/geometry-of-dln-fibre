<task>
Lean 4 + Mathlib, deep-linear-net RLCT formalisation. I need a DECORRELATED assessment: is a block-
triangular-determinant GRADING for a fused-frame derivative TRACTABLE over opaque matrix widths, or
M-DEPENDENT (a wall)? Context: a prior grading idea (layer-compatible fibre bijection) was just found
FALSE by concrete #eval (I had confirmed it on algebra alone — a discipline failure). So I need the
CONCRETE structure validated, not just the algebra.

THE MAP: a fused structural chart map `Frame_M : (Fin N → ℝ) → (Fin N → ℝ)` (N = ∑_s M_s·M_{s+1},
opaque) in a SINGLE positional row-major coordinate system (NOT a role-decoder — both input and output
are the SAME positional Fin N, so its derivative DFrame_M is a Fin N × Fin N matrix with ONE grading,
no row/col mismatch). I want |det DFrame_M| via Matrix.BlockTriangular.det = ∏ diagonal-block dets.

THE PROVEN SOUNDNESS: the dependency is one-sided — output coord at chain-LAYER s reads input coords
only at layers ≤ s (Lean-proven, the b-0 capstone). So a COARSE LAYER grading (bLayer = chain layer)
IS block-triangular. BUT the coarse layer grading has the WRONG diagonal-block determinants: the
worked (3,3,3,3) precedent uses a FINER grading frameB : Fin 27 → ℕ with 13 SCC-condensation blocks
(NOT the 3 chain-layers), block sizes [1×8, 3×4, 7]. The 7-block is the 2×2-K-core coupling
(det = (z1z4−z2z3)²), the singletons are radial/spectator (det z0/z9), the 3-blocks are chain.

THE CONCRETE FINDING (sympy SCC of T3333's dependency digraph): 11 SCC blocks, sizes [1×6, 3×4, 9] —
DIFFERENT from frameB's 13 (the hand-tuned grading differs from the raw SCC). So the grading is subtle,
NOT a simple read-off, and the block SIZES clearly depend on M's widths (the K-coupling block size
depends on the per-boundary K-core dimension t_s; the 2×2 K at (3,3,3,3) gives the 7-block).

THE QUESTION: for Matrix.BlockTriangular.det I need a SINGLE grading b : Fin N → α (LinearOrder) with
off-block-vanishing + per-block square diagonal dets I can compute (the |det K_s|^{r+c}·radial·LDU
monomials). The COARSE layer grading is proven-sound but the diagonal blocks aren't the right
per-K-core monomials. A FINER grading (SCC/frameB-style) gives the right diagonal dets but its block
structure is M-dependent (block sizes vary with the K-core widths t_s).
</task>

<output_contract>
Answer in 4 short sections:

1. Is the FINER (SCC/frameB-style) grading TRACTABLE over opaque widths, or genuinely M-DEPENDENT
   (a wall)? Specifically: can a UNIFORM grading formula b : Fin N → ℕ be written ∀M (a function of the
   positional index + M's widths), or does the SCC condensation's block STRUCTURE (which coords clump
   into the K-coupling block vs singletons) change qualitatively with M (e.g. the number/shape of blocks
   depends on the descent ranks t_s in a non-uniform way)?

2. Is there a MIDDLE grading — finer than the 3-layer (so diagonal blocks are the right per-K-core
   monomials) but UNIFORM over M (a tractable formula)? E.g. grade by (layer, role) where role ∈
   {K-core, radial-pivot, X, N, E, lift} — does a (layer, role)-lexicographic grading give block-tri
   with diagonal blocks = the per-(layer,role) monomials, uniformly? Or does the K-coupling genuinely
   span a (layer, role) block in a way that needs the finer SCC?

3. ALTERNATIVE to a single global grading: the det_comp route. Instead of ONE block-tri det, factor
   DFrame_M = ∏ (per-layer / per-role insertion CLMs) via the banked listProd_clm_abs_det telescope
   (|det ∏ fs| = ∏|det fs_i|, no casts), each factor's det a per-block monomial. Does this AVOID the
   M-dependent global grading (each factor is a local block, det computed locally), at the cost of
   proving DFrame_M = the product? Is this more tractable than the global SCC grading over opaque widths?
   (NB: a PRIOR det route F1 died because composeFold-of-DISJOINT-factors couldn't represent the chain
   COUPLING; but here the factors would be the FUSED frame's TRIANGULAR pieces, not disjoint — does that
   distinction save it?)

4. VERDICT: is Route b (fused-frame block-tri det) BOUNDED over opaque widths, or does the M-dependent
   grading make it a WALL (→ roadmap+operator)? Give the single cheapest CONCRETE check (a #eval/sympy
   at a SECOND M with different K-core widths, e.g. (2,3,2) or (4,2,2)) that would discriminate
   tractable-vs-wall, and what to look for.
</output_contract>

<grounding_rules>
Only my summary + the sympy finding. Mark unstated-fact dependencies "ASSUMPTION: …". Distinguish
"follows from your summary" vs "verify X". No Lean >5 lines. Be willing to say WALL if the grading is
genuinely M-dependent — a clean wall verdict is more valuable than a hopeful bounded claim.
