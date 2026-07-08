<task>
You are a decorrelated second opinion for a formalisation-scoping decision in a Lean 4
+ Mathlib research project. Adjudicate whether ONE specific step of a resolution-of-singularities
argument is (I) a BOUNDED, break-it-down-buildable Lean development from scratch, or (II) genuinely
needs to be admitted as a CITED interface axiom. Do NOT assume either answer; weigh both.

SETTING (exact math, no Lean needed to answer).
We must prove finiteness of a real integral (a real-log-canonical-threshold / RLCT lower bound):
  I(c') = INT_{box} ||A_0 . A_1 . ... . A_{L-1}||_F^{-2 c'} dA  <  infinity   for all c' < (1/2).minAdm(M),
where A_s are real matrices of sizes M_s x M_{s+1} (a "deep linear network" chain), ||.||_F is
Frobenius norm, and minAdm(M) is a known integer (the fibre codimension). At the deepest point one
reduces to resolving the singularity of ||prod_s C^(s)||^2 at the origin (Aoyagi 2024).

THE CONSTRUCTION UNDER TEST -- Aoyagi's recursive blow-up, "depth recursion" form.
Resolve the chain ONE BOUNDARY AT A TIME, outside-in. At each boundary you (a) put the current
outer factor into an "incidence" chart, (b) do ONE radial blow-up of the current corank block
(introducing one exceptional coordinate u for the whole block), (c) apply "regular" (unit /
invertible-at-the-chart-origin) block-elimination transforms Q, P that reduce the residual block to
diag(1, D'), producing a FRESH chain one matrix SHORTER whose loss is (monomial)^2 . (fresh core),
plus lower-order "coupled" terms delta_i^2 . ||R_i . Z||^2 that SHARE the still-unresolved deeper
factor Z = C^(k+1) . ... . C^(L). Recurse on the fresh shorter chain. Terminate at depth 1 (a single
matrix; Morse / normal-crossing), read off ||prod||^2 = sum b_i^2 (normal crossing). A per-divisor
Jacobian/exponent ledger accumulates to give RLCT = (1/2).min over branches of Mval(branch).

WHAT IS ALREADY ESTABLISHED (facts, exact-verified elsewhere):
- The VALUE is certified general-L, all branch types (= (1/2).minAdm), by 3 independent methods
  + a reduced-rank-regression anchor. This is NOT in question. Only formalisation tractability is.
- A "threshold-only" invariant (per-output-row multiplicity, no symbolic support) is PROVABLY
  insufficient at corank >= 2: the monomial ideals <dx, dy> (shared d) and <d1 x, d2 y> (separate)
  have DIFFERENT RLCT (1/2 vs 1) despite identical "light data". So the resolution MUST carry a
  per-generator symbolic divisor-support map (which exceptional coordinates divide which generator),
  including the SHARING relations.
- For a SINGLE deeper matrix (L=2 core, e.g. dimension chain (3,3,4), binding cut corank 2x2),
  the coupled resolution is explicitly verified: RLCT = 4 = (1/2).Mval, one radial blow-up realises
  the shared support natively.
- An ALTERNATIVE route ("atom route") -- integrate the corank block Gamma out over full space, producing
  a Gram-determinant weight det(Q_b Q_b^T)^{-p/2} = ||wedge^q Q_b||^{-p} of the matrix PRODUCT Q_b = A.Z,
  and then integrate the outer parameters -- is known to OVER-COUNT on the rank-drop locus {det=0}
  (a full-space-enlargement artifact) and to require principalising the maximal-minor / Gram ideal
  of a matrix PRODUCT. Mathlib lacks: Cauchy-Binet, SVD factorisation, and ANY decomposition valid
  on the rank-drop locus, and lacks resolution-of-singularities / blow-up / monomialisation entirely.

THE OPEN QUESTION (the ONE step to adjudicate):
The single-deeper-MATRIX corank-2 coupled resolution is verified. Does it extend when the deeper
factor Z is itself a PRODUCT of >= 2 matrices (Z = W1.W2), i.e. the corank-2 block couples to a
matrix PRODUCT rather than a single matrix? Concretely, resolve
   F = ||T . W1 . W2||^2  +  delta^2 . ||R . W1 . W2||^2
(T = pivot rows, R = residual rows of the layer-1 block after shear; delta = the corank exceptional).
Two sub-questions:
 (Q1) In the depth-recursion, when boundary 2 (the W1.W2 boundary) is later resolved and introduces
      its own exceptional coordinates, does the coupled term delta^2.||R.W1.W2||^2 correctly INHERIT the
      SAME exceptional coordinates as the main core ||T.W1.W2||^2 (shared support), by a FINITE
      explicit sequential chart cover -- or does correctly capturing the sharing across the deeper
      PRODUCT require a genuinely SIMULTANEOUS (non-sequential) principalisation that a finite
      explicit chart cover cannot express?
 (Q2) Do the "regular" block-elimination transforms Q, P at each boundary STAY unit / regular
      (invertible with no new poles at the chart origin) when the factor being reduced is entangled
      with the accumulated decoration from shallower boundaries AND the deeper factor is a product?
      Or can a Q, P transform become non-regular (introduce a pole / fail to be a coordinate change)
      precisely because the deeper factor is a product?

If (Q1) is "finite sequential cover suffices" and (Q2) is "transforms stay regular", the step is
BOUNDED (build it). If EITHER fails (needs simultaneous principalisation, or a non-regular transform),
the step is CITE-worthy. Adjudicate.
</task>

<output_contract>
Respond in EXACTLY these sections, terse:
1. VERDICT: one of {BUILD (bounded), CITE (needs interface axiom), MIXED} -- one line.
2. Q1 answer: sequential-finite-cover-suffices vs needs-simultaneous -- with the one-sentence reason.
3. Q2 answer: transforms-stay-regular vs can-become-non-regular -- with the one-sentence reason and,
   if they can fail, the concrete smallest failing configuration.
4. The single cheapest EXACT discriminating computation that would settle Q1/Q2 (name the matrices,
   sizes, and what quantity to compute -- e.g. a specific RLCT via the toric formula, or a symbolic
   determinant/pole check).
5. Your confidence and the single most likely way your verdict is wrong.
</output_contract>

<grounding_rules>
- Ground your answer in the exact math above. State plainly which of your claims are established
  fact vs your inference.
- Do NOT propose a Lean proof route or Mathlib tactic -- the question is math tractability
  (finite-explicit-chart vs simultaneous-principalisation), not Lean mechanics.
- The value (= (1/2).minAdm) is NOT in question; do not re-derive it. The question is ONLY whether
  the deeper-PRODUCT corank-2 coupled resolution is reachable by a finite explicit sequential chart
  construction (build) or needs a cited simultaneous-principalisation interface (cite).
- Be concrete about the sharing-across-a-product mechanism; that is the crux.
</grounding_rules>
