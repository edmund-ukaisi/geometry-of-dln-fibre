<task>
Adjudicate one analytic finiteness question arising in a resolution-of-singularities reduction for
a deep-linear-network sublevel-volume (RLCT) integral. Argue whichever way the math goes; I have
NOT told you my expected answer.

SETUP (all real matrices; frobSq(X)=sum of squares of entries; integrals are Lebesgue over boxes).
Fix integers u>=1 (a "pivot rank"), a>=1, b>=1, and "deep" widths. Consider a change-of-variables that
has already been performed, leaving the following per-cell integrand to be integrated over the front
"outer" block variables (P a u x u matrix, B12 a u x b matrix, C an a x u matrix) and a Gamma block
(a x b), at fixed reduced-chain parameters z:

  freedSchurLoss = frobSq(P . Qt) + frobSq(C . Qt + Gamma . Qb),   raised to the power -c',

where:
  - Qt (read "Q-tilde") is a u x N matrix built from z; GENERICALLY full row rank u (has a kernel since u<N).
  - Qb = A_cor . Zdeep is a b x N corank matrix; A_cor is a b x M2 box variable, Zdeep is M2 x N,
    with rank(Zdeep) >= m where the "strong-block" convergence a < m - b + 1 HOLDS (strictly).
  - P ranges over {P : P invertible} intersect a box (the pivot is NOT bounded away from 0).
  - c' > a*b/2 (strictly).

The GOAL is to show: after integrating out (P, B12, C, Gamma), the result is
   C_hle * [decorated reduced integrand],
with C_hle < infinity a FINITE constant (uniform in z over the reduced-parameter box), where the
"decorated reduced integrand" is commonDivisor^2 * frobSq(prod(reducedChain) z) times a Jacobian
monomial (the pivot energy after a P-radial blow-up P = commonDivisor * Phat, det-1 clear).

Three facts already established elsewhere (you may use them):
 (i)  the front factor [P | B12] (u x (u+b)) stays full row rank u even as det P -> 0 (B12 supplements);
      the naive per-P change of variables z0 -> P.z0 has Jacobian |det P|^{-M2} which is NON-integrable,
      but that is a domain-enlargement artifact of the WRONG decomposition.
 (ii) a banked lemma gives, for FULL-ROW-RANK R (=Qt, q columns... i.e. R is p x q with the relevant
      Gram R R^T positive definite), the anisotropic C-integral
      integral_C (w + frobSq(C.R + S))^{-c'} dC = det(R R^T)^{-p/2} . Cresid(p q) . (w + ||S(I-P_R)||^2)^{-(c' - p q/2)}.
 (iii) a banked lemma gives integral det(gram Q)^{-a/2} < infinity over a box iff (b <= q and a < q - b + 1).

QUESTIONS.
 Q1. In the STRICTLY-convergent regime a < m - b + 1 (strong block finite) with c' > a b/2, is C_hle
     genuinely FINITE and uniform in z? What are the precise failure modes (if any) for C_hle < infinity?
 Q2. Does the finiteness argument need to SPLIT on a < u vs a >= u? For a < u, is it true that the
     transverse part of the C-integral can be dropped and the residual is a sphere integral
     integral_{S} ||Qt . omega||^{-a} d(omega) that is finite IFF a < u (kernel of Qt has codim u)?
     For a >= u, must one instead keep the full C-integral and use fact (ii) (the det(Qt Qt^T)^{-a/2}
     reduced-Gram, disposed by fact (iii))? Or is one route valid for all a?
 Q3. The det P -> 0 region: does it contribute only a FINITE, vanishing-with-the-cutoff amount to C_hle
     (given (i)), or is there a residual log / power divergence from the pivot that survives?
 Q4. Is there any hidden divergence when rank(A_cor . Zdeep) < b on a positive-codimension locus inside
     the A_cor box (i.e. the corank matrix Qb degenerates), NOT covered by the strong-block bound (iii)?
</task>

<output_contract>
Answer Q1-Q4 in order, each 3-8 sentences. For each, state VERDICT (finite / not / split-needed) first,
then the reason. If you use a scalar or low-dim model to decide, give the exact exponent bookkeeping.
End with a 3-line "DECISIVE OBSTRUCTION (if any)" summary: the single cell/regime most likely to break
C_hle < infinity, and the cheapest exact check to settle it.
</output_contract>

<grounding_rules>
Distinguish PROVEN (from the banked facts i-iii or exact computation you show) from INFERENCE/heuristic.
Do not assume my expected answer. If a route only works under an extra hypothesis, name it. Flag any place
where "full row rank" is insufficient because the matrix can APPROACH rank drop within the box.
</grounding_rules>
