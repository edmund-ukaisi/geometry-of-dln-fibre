<task>
Independent adjudication of a log-canonical-threshold (RLCT) finiteness question arising in a
formal proof. Determine, by exact algebra, the convergence threshold of a constrained matrix
integral and whether it covers a stated range. Argue whichever direction the algebra supports;
hunt for a divergence. Do NOT assume the setup is sound.
</task>

<setup>
Fix a 3-term chain of positive integers M = (M0, M1, M2). Two real matrices:
  B : M0 x M1,   W : M1 x M2.
Frobenius loss f(B,W) = ||B W||_F^2 = sum of squares of entries of the product B*W.
Consider integrals of the form  I(c') = ∫∫ f(B,W)^(-c') dB dW  over specified domains.
RLCT (log-canonical threshold) λ of the integrand over a domain: I(c') < ∞  iff  c' < λ.

KNOWN FACT (established independently, treat as given): over the FULL boxes
B ∈ [-1,1]^(M0 M1), W ∈ [-1,1]^(M1 M2), the RLCT is
  λ_full = (1/2) * minAdm(M),   where minAdm(M) = min_{r=0..min(M0,M1)} [ (M0-r)(M1-r) + r*M2 ].
The minimizing r is r* (= "argmin cut"); (M0-r)(M1-r)+r*M2 is codim of {BW=0} on the rank-B=r stratum.

CONSTRAINED DOMAIN ("shell-j"): restrict W to the region S_j = { W : W has EXACTLY j singular
values < ε } for a fixed small ε>0 (the other min(M1,M2)-j singular values are ≥ ε). Also intersect
B with { det(top-left u×u block of B) ≠ 0 } (call it IsUnit-P), where u is a parameter below.
So the constrained integral is  I_j(c') = ∫_{W∈S_j, B∈box, IsUnit-P} ||BW||_F^{-2c'} dW dB.

PARAMETERS from the proof: a binding cut t* = argmin r above; a shell level j with 1 ≤ j < r where
r = min(M0 - t*, M1 - t*); the deeper cut u = t* + j; a := M0 - u, b := M1 - u.

TWO candidate "target thresholds" appear in the surrounding proof; determine which one the object must
meet and whether it does:
  (T1)  c' < (1/2) minAdm(M)                          [whole-chain]
  (T2)  c' < ( minAdm(u,M2) + a*b ) / 2 = (u*M2 + ab)/2  [per-cut: reduced 2-chain (u,M2) leaf + corner ab]
It is an algebraic fact that minAdm(M) ≤ ab + minAdm(u,M2) = ab + u*M2, so (1/2)minAdm(M) ≤ (T2).
The surrounding proof produces a domination  I_j(c') ≤ C · G(c' - ab/2)  with C < ∞, where G is a
"reduced comparator" whose own RLCT is (1/2) minAdm(u,M2) = u*M2/2, i.e. G(e) < ∞ iff e < u*M2/2.
</setup>

<questions>
Q1. Compute the RLCT λ_j of the shell-j constrained integral I_j(c') EXACTLY, as a function of
   (M0,M1,M2,j). Explain how the shell-j restriction (exactly j small singular values of W) changes
   the resolution/stratification relative to the full box. Does IsUnit-P (co-null in B) change the
   VALUE of the integral at all?
Q2. Give λ_j for M=(6,6,6) at j=1 (u=4) and j=2 (u=5); and for M=(4,4,4) at j=1 (u=3);
   and M=(8,8,8) at j=1,2,3. Compare each λ_j against BOTH (T1)=½minAdm(M) and (T2)=(u M2+ab)/2.
Q3. For a FIXED c', when is a domination I_j(c') ≤ C·G(c'-ab/2) with C<∞ TRUE vs FALSE, in terms of
   whether the LHS and the comparator G(c'-ab/2) are finite? Identify the exact c'-interval (if any)
   where the comparator is finite but I_j diverges (that would make the domination false).
Q4. If the surrounding mountain proves whole-chain finiteness for c' < ½minAdm(M) and invokes the
   domination only for such c', is there any j in [1,r) and any c' < ½minAdm(M) at which I_j(c')
   diverges (a genuine wall)? Or is I_j finite on all of c' < ½minAdm(M) for every such j?
</questions>

<output_contract>
- Label every statement [FACT] (exact algebra you can defend) or [INFERENCE].
- Give λ_j as exact rationals for the requested cases with the codim arithmetic shown.
- State plainly: is there a divergence of I_j at some c' < ½minAdm(M) for some 1≤j<r? YES/NO + the case.
- Separately: is there a divergence at some c' < (T2) for some 1≤j<r? YES/NO + the case.
- Do NOT optimize for agreement; if the algebra points to a wall, say so and give the exact config.
</output_contract>

<grounding_rules>
- Exact algebra only (rationals / codim counts / singular-value stratification). No floats as proof.
- The RLCT of a matrix-product loss over a domain is governed by the deepest singular stratum
  REACHABLE within that domain's closure; a domain restriction can only RAISE the RLCT.
- "Exactly j small singular values" caps the number of singular values of W that can → 0 at j.
</grounding_rules>
