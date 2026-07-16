<task>
Compute the exact convergence threshold (real log-canonical threshold, RLCT) of a Lebesgue integral
over matrix boxes, and compare it to a claimed value. Be exact; use resolution of singularities /
Newton polytope / the codimension-of-the-analytic-set argument. Monte-Carlo only to sanity-check.
</task>

<object>
Fix integers M0, M1, M2 >= 1 and a cut u with 1 <= u <= min(M0,M1). Write a = M0-u, b = M1-u.
Consider three real matrices ranging over entrywise boxes [-1,1]^(entries):
  * z0   : u  x M2   (call it the "pivot block")
  * Acor : b  x M2   (call it the "corank block")
  * B    : M0 x M1   (full)
Form  W = [ z0 ; Acor ]  (an M1 x M2 matrix, stacking z0 on top of Acor; note u+b = M1).
The integrand is  f(z0,Acor,B) = || B * W ||_F^2   (squared Frobenius norm of the M0 x M2 product B*W).
Define  I(c) = \int_{boxes} f^{-c} dz0 dAcor dB .

QUESTION 1. For which real c > 0 is I(c) < infinity? Give the exact supremum threshold lambda*
(so I(c) < infinity iff c < lambda*). Express lambda* in closed form in terms of M0,M1,M2.

QUESTION 2. Evaluate lambda* for the three concrete cases:
   (A) (M0,M1,M2,u) = (3,3,3,2)
   (B) (M0,M1,M2,u) = (4,4,4,3)
   (C) (M0,M1,M2,u) = (6,6,6,4)

QUESTION 3. A separate proposed formula for the threshold is
   lambda_claim = ( u*M2 + a*b ) / 2 ,   a=M0-u, b=M1-u.
For each of (A),(B),(C), state whether lambda_claim is EQUAL to, ABOVE, or BELOW your lambda* from Q2,
and give the numbers.
</object>

<grounding_rules>
- Since W = [z0;Acor] ranges over the FULL box of M1 x M2 matrices (z0 and Acor together fill all M1 rows),
  and B ranges over the full M0 x M1 box, the pair (B, W) ranges over full boxes independently. So I(c) is
  the integral of ||B W||_F^{-2c} over full boxes of an M0 x M1 matrix B and an M1 x M2 matrix W.
- The singular locus is { B W = 0 }. Use: the RLCT of ||F||^2 for an analytic map F equals the min over
  points of the local RLCT; at a SMOOTH point of {F=0} of codimension C the local RLCT is C/2; and globally
  RLCT <= (codim of {F=0})/2 always. You may use known results on the codimension / learning coefficient of
  the product-of-two-matrices ("reduced-rank regression", Aoyagi-Watanabe) variety {BW=0}.
- Compute codim{BW=0} exactly by stratifying on rank(B).
- Report FACTS (exact algebra) vs INFERENCES separately. Do not assume the proposed formula in Q3 is right.
- If you use rlct=codim/2 vs rlct<codim/2, say which and why.
</grounding_rules>

<output_contract>
1. lambda* closed form (Q1) with derivation (codim computation + why rlct equals or is below codim/2).
2. Table for (A),(B),(C): codim{BW=0}, lambda*, lambda_claim, and EQUAL/ABOVE/BELOW.
3. One-line verdict per case: is lambda_claim a SOUND lower bound for convergence (lambda_claim <= lambda*)
   or does it OVERCLAIM (lambda_claim > lambda*, so I(c) diverges for some c < lambda_claim)?
</output_contract>
