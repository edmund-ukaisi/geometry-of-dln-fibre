<task>
Adjudicate ONE question about a Lean dependency, with exact reasoning. Do NOT run code.

SETTING. Deep-linear-network loss F(A) = ||prod(A) - B||^2, prod(A)=A^(1)...A^(L), layer A^(s) of size
M^s x M^{s+1}, B rank r. To prove "D1>=" (the local RLCT at the deepest fibre point <= at any other
fibre point v), a prerequisite (a) is a local normal form at an ARBITRARY fibre point v:
   F(v + W) = [regular block: nondegenerate sum of q squares] + [homogeneous residual core]
where q = rank of the generator-map Jacobian at v.

A formaliser found Mathlib v4.29 LACKS the general CONSTANT-RANK theorem / Morse lemma (rank-constancy
on a neighbourhood + the implicit function theorem packaging), so building it is a Mathlib-contribution-
scale detour. The project has a strict "only cite S2 (a bare monomial integral); prove everything else"
mandate, so a cited constant-rank sorry is not allowed.

THE QUESTION: is the general constant-rank theorem GENUINELY ESSENTIAL for prereq-(a) at arbitrary v,
or is there an ELEMENTARY family-specific route exploiting the DLN chain-product / bilinear-generator
structure, that avoids the general theorem?

FACTS I established by exact computation:
- The generators (entries of prod(v+W) - B) are POLYNOMIAL (multilinear in the layer perturbations W).
- At v, an EXPLICIT gauge element (a finite matrix factorization P·B·Q = rank-r corner block, already
  proven in Lean, NO constant-rank theorem) moves v to block-normal form: the regular block becomes the
  rank-r IDENTITY corner, whose linear perturbation has IDENTITY (unit-diagonal) linear part; the
  residual core has NO linear part (homogeneous).
- Solving the q regular generators is then a TRIANGULAR sequence of one-variable analytic implicit
  solves, each with a UNIT linear coefficient (pivot). Verified concretely: e.g. for an L=3 (2,2,2,2)
  intermediate fibre point, solving the regular generators gave explicit RATIONAL functions with UNIT
  denominators (w0+1, w0·w8+w0+w8+1 — both units near 0), i.e. analytic, no general IFT needed.
- So the structure is: gauge to unit-pivot triangular form (explicit matrix factorization), then a
  triangular sequence of 1-variable unit-derivative analytic implicit solves, then the homogeneous core
  remains. This is much lighter than the general constant-rank theorem.
</task>

<sub_question>
1. Is the general constant-rank/Morse theorem GENUINELY ESSENTIAL for prereq-(a), or does the DLN chain
   structure (the explicit gauge to a rank-r identity corner + triangular unit-pivot elimination) give
   an elementary route that avoids it?
2. Precisely what Lean ingredient does the elementary route need, and is it lighter than constant-rank?
   Candidates: (i) the 1-variable analytic/smooth inverse-or-implicit-function theorem for a map with
   unit (nonzero) derivative; (ii) iterated triangularly. Does Mathlib v4.29 plausibly have (i) (e.g.
   via HasFDerivAt + the inverse function theorem for invertible-fderiv maps, ContDiff/analytic), so the
   elementary route is buildable WITHOUT a Mathlib-scale constant-rank contribution?
3. The catch to check: the general constant-rank theorem's extra content (beyond triangular unit-pivot
   elimination) is handling NON-triangular rank-constancy / the rank being locally constant but the
   pivots NOT separable. Does the DLN family AVOID that — i.e. does the gauge + chain structure ALWAYS
   give a triangular unit-pivot order, so the non-triangular case never arises? Or is there a fibre
   point v where the regular block does NOT triangularize and the general theorem IS needed?
4. Verdict: D1>= cheaply revivable (elementary triangular route, no Mathlib-scale build) OR genuinely
   gated on a Mathlib-scale constant-rank contribution. With the precise reason.
</sub_question>

<output_contract>
- Verdict: constant-rank ESSENTIAL (Mathlib-scale, roadmap stands) or ELEMENTARY route exists (cheaply
  revivable), with the precise reason.
- The exact lighter Lean ingredient the elementary route needs, and whether Mathlib v4.29 plausibly has it.
- Whether the chain family ALWAYS triangularizes (avoiding the non-triangular constant-rank case) or has
  a v where the general theorem is unavoidable.
- FACT vs INFERENCE labels.
</output_contract>

<grounding_rules>
- Ground in the facts above + standard analysis (implicit/inverse function theorem, Morse/constant-rank)
  and rough knowledge of Mathlib's analysis library (HasFDerivAt, inverse function theorem for invertible
  fderiv, ContDiff, analytic functions). Reason on paper ONLY; do NOT read files or run code.
- "constant-rank theorem" = the general result: a C^k map of locally constant rank q is, in suitable
  local coords, (x_1..x_q, 0..0). "triangular unit-pivot elimination" = solving generators one at a time,
  each with a unit linear coefficient, the analytic implicit solution being a unit-denominator series.
- Preserve FACT vs INFERENCE. Name any hypothesis a claim needs.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication.
</important>
