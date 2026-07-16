<task>
Exact-algebra RLCT / real-log-canonical-threshold question about a deep-linear-network Frobenius-loss
box integral, and whether a specific WEIGHTED induction reaches the sharp threshold.

SETUP (square chain, arity 4). For n >= 2 consider three independent n x n real matrices P, Z0, W,
each entry ranging over the unit box [-1,1]. Define the box integral

    I_n(c) = ∫∫∫  frobSq(P · Z0 · W)^(-c)   dP dZ0 dW,     frobSq(A) = sum of squares of entries of A.

FACT (Aoyagi; take as given): the real log canonical threshold of frobSq(P·Z0·W) at the origin is
lambda_n = (1/2) * minAdm(n,n,n,n), so I_n(c) < ∞  iff  c < lambda_n. Here minAdm is the exact-integer
recursion
   minAdm(M) = M0*M1                          if M has 2 widths
   minAdm(M) = min_{0<=t<=min(M0,M1)} [ (M0-t)(M1-t) + minAdm(t, M2, M3, ...) ]   (>=3 widths)
Values: minAdm(2,2,2,2)=3, minAdm(3,3,3,3)=6, minAdm(4,4,4,4)=11, minAdm(5,5,5,5)=17.
So lambda_3 = 3, lambda_4 = 11/2.

TWO EXACT DECOMPOSITIONS OF lambda_n (both verified numerically-exact):

(A) JOINT RANK STRATIFICATION of the middle product Y = P·Z0 (n x n). Stratify by rank(Y)=r'
    (corank k = n-r'). The product-corank-k locus of Y has codimension C_k = k^2 - floor(k^2/4)
    (smaller than k^2 because EITHER factor can drop rank). The rank-r' chart contributes threshold
    (C_k + n*r')/2, and  min over r' of (C_k + n*r')/2 = lambda_n  EXACTLY. For n=3 the binding
    stratum is r'=1 (corank k=2): (C_2 + 3)/2 = (3+3)/2 = 3. For n=4 the binding strata are k=2,3.

(B) SINGLE-CUT PEEL + RECURSION on chain arity. At the "binding cut" t* (the minimiser of the minAdm
    recursion), Schur-eliminate the invertible t* x t* pivot block of P; the corank block is a x b =
    (n-t*) x (n-t*). The reduced problem is the chain (t*, n, n) one arity shorter. The budget splits
    EXACTLY as  lambda_n = (a*b)/2  +  (1/2)*minAdm(t*, n, n). For (3,3,3,3): t*=2, a=b=1, budget
    1/2 + 5/2 = 3. For (4,4,4,4): t*=2, a=b=2, budget 2 + 7/2 = 11/2. Recursing, (4,4,4,4)->(2,4,4)
    ->(1,4). The corank block at the binding cut has size a=b = floor(n/2), so it GROWS with n (=2 for
    n in {4,5,6}, =3 for n in {7,8}).

THE STRUCTURE OF ONE PEEL. On the invertible-pivot chart the Schur-welded loss is
    freedSchurLoss = frobSq(B0) + frobSq(C'·B0 + Γ·Q_b)
where B0 = P·(reduced leading product), C' = C·P^{-1}, Γ is the a x b corank block, and Q_b is the
b-row part of the deeper tail (b x q). Integrating Γ:
  - Regime A (c < a*b/2): the Γ integral is finite pointwise (a clean Morse quadratic in Γ), spends a*b/2.
  - Regime B (c > a*b/2): the Γ integral, when Q_b is full row rank, is finite; but ∫_Γ frobSq(Γ·Q_b)^{-c}
    ≍ det(Q_b Q_b^T)^{-(c - a*b/2 + ...)} — a GRAM WEIGHT on the deeper tail. Q_b then ranges over its
    own box; det(Q_b Q_b^T)^{-power} is singular on {rank Q_b < b}.

THE OBSTRUCTION (independently observed). If one tries to close regime B with the UNWEIGHTED reduced-
chain finiteness (i.e. Hölder-split off det(Q_b Q_b^T)^{-power} in L^p and apply the plain box-integral
bound to frobSq^{-cq}), the split loses: the pushforward density of the n x n product Y=P·Z0 near a
corank-2 point behaves like dist^{-1} on a codim-4 locus, so it lies in L^p only for p < 4, forcing the
Hölder conjugate q > 4/3, and the reachable threshold drops to (3/4)*(1/2)*minAdm(n,n,n) < lambda_n
(for n=3: reaches 21/8 = 2.625 < 3). So the plain unweighted induction UNDERSHOOTS for every n >= 3.

THE QUESTION. Consider instead a WEIGHTED induction: the induction hypothesis is finiteness, below the
reduced chain's own threshold (1/2)*minAdm(t*,n,n), of the reduced-chain box integral CARRYING the Gram
weight det(Q_b Q_b^T)^{-power} as an attached factor (equivalently, after an R-blowup / SVD of the
corank block against the deeper tail, the weight becomes a MONOMIAL prod |u_l|^{h_l} in resolved
coordinates times a coercive residual frobSq(Γ_hat · Z)). Keep the weight ATTACHED through the
recursion rather than Hölder-splitting it off.

  Q1. Does the weighted induction REACH the full lambda_n at the square binding-cut peel for corank
      a=b >= 2 (i.e. n >= 4)? Or is there a residual DEFICIT that even the attached-Gram induction cannot
      close? Give the exact per-level budget accounting: what threshold does one peel spend on the
      corank block (regime B, Q_b degenerate strata included) and what is handed to the reduced chain,
      and does it sum to lambda_n WITHOUT slack?

  Q2. Is the corank-2 (dist^{-1}, codim-4, ρ∉L^4) obstruction EXACTLY compensated by attaching the Gram
      weight (i.e. is the deficit of the plain route exactly the "weight budget" the attached-Gram
      induction recovers), or does keeping the weight attached introduce a NEW obstruction (e.g. the
      Gram weight's own singular locus {rank Q_b < b}, for b >= 2, is not resolvable by a single radial
      blow-up of the corank block and needs a further determinantal stratification the single peel does
      not perform)?

  Q3. Specifically for the a=b=2 corank block (n=4): is one peel enough, or does the 2x2 corank block Γ
      (whose own rank can be 0,1,2) require an INTERNAL rank stratification (a nested blow-up) inside the
      peel — so that the "single peel at the binding cut" is really a multi-step resolution? A single
      radial blow-up of Γ (one radial coordinate u0, Γ = u0·Γ_hat) resolves only the origin Γ=0, not the
      rank-1 cone of a 2x2 block. Does the reduced-chain recursion pick up the rank-1 cone, or is it a gap?

  Q4. Net: is the "attached-Gram / decorated weighted induction" a COMPLETE proof route to lambda_n for
      all square chains (n arbitrary), or does it have a genuine gap at corank >= 2 that would force
      either (i) an internal determinantal stratification per peel, or (ii) citing the Aoyagi RLCT
      equality directly for the square case?
</task>

<output_contract>
Answer Q1-Q4 in order, each a short paragraph. For each: state clearly whether your claim is a PROVEN
consequence of the exact accounting you show, or an INFERENCE / heuristic. Where you assert a budget
sums exactly, SHOW the arithmetic. If you find a deficit or a gap, give the smallest n and corank where
it first bites, with numbers. End with a one-line verdict: COMPLETE-ROUTE / GAP-AT-CORANK-k / DEFICIT.
Do not assume the conclusion I am hoping for; I have deliberately withheld my own tentative verdict.
</output_contract>

<grounding_rules>
Distinguish exact-arithmetic facts (the minAdm recursion, C_k, the budget sums — you can recompute these)
from analytic inferences about integrability (the Gram convergence, the blow-up resolving a stratum).
Flag every analytic claim as INFERENCE unless it follows from a standard determinantal-integral fact
you can state precisely (e.g. the exact convergence exponent of ∫_{X box, m x q} det(X X^T)^{-s} dX).
Do not paste Lean or long code. The determinantal / Wishart integral convergence threshold is the crux —
state the exact condition you use.
</grounding_rules>
