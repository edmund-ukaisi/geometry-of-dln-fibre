<task>
Sharp integrability question deciding whether a resolution route is SELF-SIMILAR (bottoms out on an
induction) or needs an external citation. Deep-linear-network Frobenius-loss box integral.

CONTEXT. Square chain (n,n,n,n): P, Z0, W independent n x n matrices, entries in [-1,1]. RLCT of
frobSq(P Z0 W) is lambda_n = (1/2) minAdm(n,n,n,n). lambda_3 = 3, lambda_4 = 11/2. A resolution peels the
first layer at the "binding cut" t* (invertible t* x t* pivot P2 of P). The corank block is Gamma
(c x c, c = n - t* = ceil(n/3), so c>=2 for n>=4). After a Schur weld, on the invertible-pivot chart the
loss is EXACTLY

    L = frobSq(B0) + frobSq(C' B0 + Gamma Q_b)

where B0 = P2 * Qtilde (the reduced leading product, t* x q), C' = C P2^{-1} (c x t*), Gamma is the
c x c corank block, Q_b is the c-row tail block (c x q). B0 and Q_b are BOTH built from the deeper layer
variables (they share deeper variables); C' involves the bottom block C of P. The reduced chain is
(t*, n, n) one arity shorter; the intended budget is  lambda_n = (c^2)/2 + (1/2) minAdm(t*, n, n),
EXACT (n=4: 2 + 7/2 = 11/2).

KNOWN. Integrating Gamma on {rank Q_b = r}: after an SVD Q_b = U [Qhat; 0] (Qhat r x q, full rank r),
Gamma U splits into a x r "active" columns and a x (b-r) "free" columns. Completing the square in the
active part (valid because Qhat has full row rank r), one gets, with F = frobSq(B0) + frobSq(Pperp(C'B0)):

    integral over Gamma  =  (free volume, a*(b-r) dims) * det(Qhat Qhat^T)^{-a/2} * F^{-(c - a r / 2)} * const

where Pperp(C' B0) = C' B0 (I_q - Q_b^+ Q_b) is the component of the coupling C'B0 ORTHOGONAL to the row
space of Q_b. So the reduced integrand on the rank-r stratum is

    det(Qhat Qhat^T)^{-a/2} * ( frobSq(B0) + frobSq(C' B0 * Pi) )^{-(c - a r/2)},   Pi = I - Q_b^+ Q_b.

The Gram weight det(Qhat Qhat^T)^{-a/2} is the determinantal weight the induction must CARRY. The base
frobSq(B0) + frobSq(C' B0 * Pi) is a SUM: the reduced-chain loss frobSq(B0) PLUS a coupling remainder
frobSq(C' B0 * Pi) whose projector Pi = I - Q_b^+ Q_b DEPENDS ON rank(Q_b) (the deeper tail's rank).

THE DECIDING QUESTION. Two options for closing this by an induction on chain arity:
  (a) SELF-SIMILAR: the coupling remainder frobSq(C' B0 * Pi) can be DROPPED as a nonnegative term
      (base >= frobSq(B0)), so the reduced integrand is <= det(Qhat Qhat^T)^{-a/2} * frobSq(B0)^{-(c-ar/2)},
      a Gram-WEIGHTED instance of the reduced chain that the (decorated, weight-carrying) arity-IH closes.
      This bottoms out (each corank block reduces to a smaller Gram-weighted box-instance).
  (b) NOT self-similar: dropping frobSq(C' B0 * Pi) LOSES — the upper bound
      integral det(Qhat Qhat^T)^{-a/2} * frobSq(B0)^{-(c-ar/2)} DIVERGES before lambda_n, so the coupling
      remainder is LOAD-BEARING (its extra decay is needed to reach lambda_n). Then the object is a
      genuinely coupled determinantal-incidence integral of B0 and Q_b, NOT a Gram-weighted reduced chain.

  Q1. Is the coupling remainder frobSq(C' B0 * Pi) DROPPABLE (option a) or LOAD-BEARING (option b)?
      Decide by computing the threshold of the DROPPED-coupling object
         J_drop(c) = integral_{deeper box}  det(Q_b Q_b^T)^{-a/2} * frobSq(B0)^{-(c - (contrib))}
      (stratified over rank Q_b), i.e. the Gram-weighted reduced chain WITHOUT the coupling. Does
      J_drop reach lambda_n, or does it fall short? Use the exact Wishart/determinantal criterion
      integral_{X box, m x q} det(X X^T)^{-s} dX < inf  iff  2s < q - m + 1, and the reduced-chain RLCT
      (1/2) minAdm(t*, n, n). Give the arithmetic for n=4 (t*=2, c=2), and say whether the min over
      rank-strata reaches 11/2.

  Q2. If option (a): does the Gram-weighted induction BOTTOM OUT? I.e. is
      "reduced chain redChain(t*,M) carrying a det-Gram weight of charge a/2 on its leading corank rows"
      itself an instance of the SAME weighted finiteness for a shorter chain, so the recursion terminates
      at width-2 (where the Gram is trivial)? State whether the det-Gram weight for c>=2 needs a FULL
      determinantal (multi-exceptional-coordinate SVD) resolution vs a single radial coordinate, and
      whether that resolution is bounded (finite # of blow-ups per peel) or itself unbounded.

  Q3. If option (b): pin the EXACT minimal statement that must be cited/proved externally — the smallest
      determinantal-incidence finiteness (in terms of a, b=c, q, and the threshold) that the arity-IH
      cannot supply. Is it exactly "the coupled corank-Gram box-finiteness at corank >= 2"?

  Q4. Net verdict: SELF-SIMILAR (option a) or COUPLING-BREAKS (option b)? If (a), is the nested build
      BOUNDED? If (b), is the minimal cited object exactly the corank-Gram determinantal-incidence?
</task>

<output_contract>
Answer Q1-Q4 in order. For Q1 SHOW the threshold arithmetic for n=4 explicitly (the min over rank-Q_b
strata of the dropped-coupling threshold) and compare to 11/2. Flag each claim PROVEN (from the stated
determinantal criterion + arithmetic) vs INFERENCE. End with a one-line verdict:
SELF-SIMILAR-BOUNDED / SELF-SIMILAR-UNBOUNDED / COUPLING-BREAKS-CITE-<exact object>.
I have deliberately withheld my own tentative verdict; do not assume it.
</output_contract>

<grounding_rules>
The load-bearing crux is Q1: whether dropping the nonnegative coupling remainder still reaches lambda_n.
This is a THRESHOLD comparison you can compute exactly from the Wishart criterion + the minAdm arithmetic.
Distinguish that exact computation from any inference about blow-up resolution. State the exact Wishart
convergence exponent you use. Do not paste Lean or long code.
</grounding_rules>
