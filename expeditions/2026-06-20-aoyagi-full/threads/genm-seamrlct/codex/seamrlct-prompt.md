<task>
Adjudicate a real-log-canonical-threshold (RLCT) question for deep linear networks (DLN). Argue
whichever way the mathematics goes — I want the honest verdict, not confirmation. Give exact algebra.

SETUP. A DLN square loss is K(A) = ||L_{p-1} L_{p-2} ... L_0||_F^2, the squared Frobenius norm of a
product of composable real matrices (layer i is v_i x v_{i+1}). Its zero set is the fiber
mult^{-1}(0). The RLCT lambda = sup{ s : |K|^{-s} locally integrable }; equivalently the integral
∫ K^{-c} over a neighborhood of a zero converges iff c < lambda. Watanabe's universal bound:
lambda_x <= codim_x(K^{-1}(0)) / 2 at every zero x. It is a THEOREM (Aoyagi, reformulated by
Lehalleur–Rimanyi 2024) that the GLOBAL rlct of a DLN loss equals codim/2 (saturates the bound); the
LOCAL statement lambda_x = codim_x/2 at every point x of the fiber is stated as an OPEN CONJECTURE in
that paper.

Standard tools I will use (all from Lehalleur–Rimanyi Prop 4.x / Watanabe):
 (S1) DISJOINT-variable sum: for F(x)>=0, G(y)>=0 with disjoint variable sets,
      rlct(F+G) = rlct(F) + rlct(G).
 (S2) DISJOINT-variable product: rlct(F*G) = min(rlct(F), rlct(G)).
 (S3) rlct is invariant under a bounded-factor equivalence c1*f <= g <= c2*f (c1,c2>0) and under
      analytic changes of coordinates with nonvanishing Jacobian on the chart.
 (S4) rlct(sum of e independent squares) = e/2 = codim/2.

THE MECHANISM UNDER TEST (a "telescoping-Schur" resolution of the rank-drop stratum
{rank(product) = rho - k}). Peel the last layer M (n x d), pick a size-r invertible pivot block
Delta, form the Schur transverse coordinate E = W - V Delta^{-1} U (so {rank M <= r} = {E=0}); on the
FREE preceding layer L do a unit-Jacobian column change so that L*M = ( H*Delta , H*U + F*E ), where
H (the "reduced last layer") is free, F (a "spectator") is free, E is the transverse Schur block, and
Delta,U,V are GENERIC (bounded away from degeneracy on the big cell). Composing through the earlier
head product P (= product of the layers before L), the loss becomes
      loss  =  || P * ( H*Delta , H*U + F*E ) ||_F^2 .

The WORRY: the bilinear PRODUCT seam F*E means the loss is NOT normal-crossing on a single chart. The
paper's caution: codim = C does NOT imply rlct = C/2 for free (e.g. x^2 + y^4 has zero-set codim 2 but
rlct 3/4 < 1). Could some rank-drop stratum + seam behave like x^2+y^4 (a higher-order tangency that
pushes the local rlct BELOW codim/2), or is every stratum's transverse loss quadratic-nondegenerate
per component so that rlct = (min-codim component)/2 = C_k/2?

SPECIFIC SUBQUESTIONS (answer each; exact algebra, cite which of S1–S4 you use):

Q1. rlct of the single-peel model with TRIVIAL head (P = identity):
    loss = ||H||^2 + ||F*E||^2, with H in R^{m x r} free, F in R^{m x (n-r)} free, E in R^{(n-r)x(d-r)}
    free. Reduce via S1/S2. In particular is rlct(||F*E||^2) = codim{FE=0}/2 for a general matrix
    product F*E? (This is itself a 2-layer DLN loss.) Give the value for (m,n-r,d-r) = (2,1,1),
    (2,2,2), (3,2,3), (2,3,2). Does it EVER fall below codim/2?

Q2. The CROSS-PEEL COUPLING. With a nontrivial head P (itself a product of degenerating layers), the
    loss is || P*[ H | F*E ] ||^2 (concatenating the r free columns H with the (d-r) product columns
    F*E). Now P is SHARED between the "reduced last layer" block H and the seam block F*E, so S1 does
    NOT directly apply (the terms are not in disjoint variables). Does the shared head break
    additivity? Is there an inductive framing (peel-by-peel) in which rlct still telescopes to
    sum_j codim_j / 2 = CR/2, or can the coupling lower the exponent? Consider the two-peel chains
    (2,2,2,2) and (2,3,3,3) (widths). Is P generically full row-rank on the big cell, and does that
    decouple it (bounded injective => S3)?

Q3. NON-COMPARABLE SCALINGS. If the transverse coordinates E_j (one per peel) and spectators F_j can
    go to zero at DIFFERENT rates t^{alpha_j}, can a non-comparable sector give a strictly smaller
    volume exponent than the comparable scaling (all alpha_j equal)? For a sum of the form
    sum_j || (stuff)_j ||^2 with each block quadratic-nondegenerate, is the minimizing scaling always
    the comparable one?

Q4. A COUPLED positive-definite metric charge. The full integrand carries a factor
    det(Q Q^T)^{-a/2} with Q = A_cor * Z where Z is the (degenerating) product and A_cor is a fixed
    b x M generic matrix; on the big cell Z = Z_red * D with D = [Delta | U] full row rank, so
    Q Q^T = N (D D^T) N^T with N = A_cor Z_red and D D^T positive definite. On a compact subchart
    lambda I <= D D^T <= Lambda I. Does this coupling change the leading corank exponent of the charge
    vs the uncoupled det(N N^T)^{-a/2}, or is it a bounded factor (S3) that leaves the rlct unchanged?

Q5. THE KILL TEST. Try to CONSTRUCT a DLN rank-drop stratum, within the scope a+b <= rho-1
    (rho = min deep width; a,b >= 1; strict shell 1 <= j < r), whose LOCAL rlct is strictly less than
    its local codim/2 — i.e. a genuine higher-order seam. If you can, give it exactly (widths, the
    stratum, the offending direction, the exponent gap). If you believe none exists in scope, give the
    cleanest sufficient condition that rules it out.
</task>

<output_contract>
- For each of Q1–Q5: a labeled verdict [BENIGN / HIGHER-ORDER / DEPENDS], the exact rlct value(s) or
  the counterexample, and which of S1–S4 (or a resolution/Newton-polyhedron argument) you used.
- Mark each claim [FACT] (exact algebra you can defend) vs [INFERENCE] (heuristic).
- End with: the single most likely place (if any) the per-stratum rlct could drop below codim/2, and
  the cleanest sufficient condition under which it provably equals codim/2.
- Do NOT assume the answer is benign because Aoyagi's GLOBAL theorem exists — the question is about the
  LOCAL per-stratum behavior on these explicit charts (the open-conjecture regime).
</output_contract>

<grounding_rules>
- Real analytic RLCT over R (not the complex lct). Frobenius norm squared losses, real matrices.
- codim means codimension of the zero set in the real parameter space (parameter-space CR codim, the
  composite-rank recursion — NOT the determinantal (M-s)(n-s) which over-counts for matrix products).
- "Quadratic-nondegenerate per component" means: near a generic point of each irreducible component of
  the chart's zero-locus, the transverse loss is a genuine sum of squares (Morse-Bott), so that
  component contributes codim/2.
- Give exact rationals. If you invoke a resolution, state the weights/Newton polyhedron.
</grounding_rules>
