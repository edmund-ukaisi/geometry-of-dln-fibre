<task>
We are formalising (in Lean 4 + Mathlib) the upper-bound finiteness ("hfin") leg of a real-log-canonical-
threshold computation for deep linear networks. I want a decorrelated reachability/cost read on ONE
sub-question, plus the heaviest sub-piece in the overall recursion. Reason from the math; do not assume my
conclusion.

THE OBJECT.  Fix matrices R : r x r (real), S : r x p (real).  frobSq(X) = sum of squares of all entries.
We integrate, over a bounded box, the integrand  frobSq(R*S)^(-c')  for a real exponent 0 < c' < theta,
where theta = (1/2)*minAdm is the (separately established) correct RLCT threshold for this core. "hfin"
means: prove this integral is FINITE for every c' < theta.

THE RECURSION (proposed general route).  Cover R-space by max-modulus-minor OPEN cells. On the cell where
the top-left k x k block M11 is a MAX-MODULUS k-minor of R and det M11 != 0 (a bounded "complete-pivoting"
cell, |R_ab| <= 1), block-Gauss-eliminate to the Schur complement  Sc = M22 - M21*M11^{-1}*M12
(size (r-k) x (r-k)). With the det-1 column reparam S = U*(P;Q), U = [[I, -M11^{-1} M12],[0,I]]:
   (R*S)_top = M11*P            (top k rows of R*S)
   (R*S)_bot = M21*P + Sc*Q     (bottom r-k rows)
   frobSq(R*S) = frobSq(M11*P) + frobSq(M21*P + Sc*Q).
The proposed comparison ("N2b") sandwiches frobSq(R*S) two-sidedly between c0*D and c1*D where
   D = frobSq(M11*P) + frobSq(Sc*Q) = frobSq((R*S)_top) + frobSq(Sc * S_bot).
Then one recurses on the corank-(r-k) core frobSq(Sc*Q), terminating at Morse leaves.

KNOWN FACTS (established here, treat as given):
 - The threshold VALUE (1/2)*minAdm is correct (proven separately).
 - On the max-modulus-minor cell, each entry of M21*M11^{-1} satisfies |.| <= 1 (classical complete-pivoting
   Cramer bound; we verified it exactly).
 - A separate "threshold-only" recursion (per-row weight multiplicity, NO symbolic divisor-sharing data)
   is PROVABLY INSUFFICIENT at corank >= 2 for getting the threshold VALUE right: it cannot encode WHICH
   divisor variables are shared, and sharing changes the Newton polytope (e.g. <dx,dy> has rlct 1/2 but
   <d1 x, d2 y> has rlct 1, identical "light" data).  [This is a VALUE-level break.]
 - Two concrete corank-2 hfin instances are already proven sorry-free, by DIFFERENT mechanisms:
   (i) an iterated matrix-fibre peel  int_X frobSq(X*Y)^(-c') <= const * frobSq(Y)^(-c')  for c' < (rows X)/2
       (no Schur split at all), and
   (ii) an explicit per-chart one-sided lower bound  frobSq(R*A1) >= (1/5)*(frobSq(top) + frobSq(Schur-bot))
        on the bounded cell, then a change-of-variables.
</task>

<output_contract>
Answer these, each with a crisp verdict + the reasoning:

Q1. For the FINITENESS (hfin) goal, which DIRECTION(s) of the N2b sandwich are actually needed? Is the
    two-sided sandwich required, or does one direction suffice? State which.

Q2. Does the needed direction hold with a UNIFORM positive constant at corank >= 2 (i.e. (r-k) >= 2),
    on the bounded complete-pivoting cell? In particular: can the bottom block  M21*P + Sc*Q  be small
    while  Sc*Q  is large (cancellation), and if so is the resulting ratio still bounded away from 0
    uniformly over the cell?  Give the mechanism and, if it holds, the form of the constant.

Q3. Rank the heaviest sub-piece of the WHOLE general-r hfin recursion among:
      (a) the N2b uniform comparison (the matrix-algebra / Schur split),
      (b) the WellFounded-on-corank recStep assembly (the measure-theoretic recursion bookkeeping,
          nested minor-pivot cover at each level, depth-r),
      (c) the depth-r Tonelli/Fubini cover plumbing + per-chart change-of-variables.
    Say which is heaviest and why, in Lean-formalisation cost terms (not just math difficulty).

Q4. Classify the overall general-r hfin upper leg: build-ready tide / needs-design-then-build / research
    wall. Name the single thing most likely to make an optimistic read WRONG.
</output_contract>

<grounding_rules>
 - Reason in exact algebra. Distinguish a FACT you derive from an INFERENCE/guess; label each.
 - Do not assume the comparison holds or fails; derive it.
 - If you write code, it must be runnable and you must say what it would show; I will run it myself.
 - "minAdm", "rlctAtOn", "monomial_rlct" are project-internal names; reason about the integrals/matrices.
</grounding_rules>
