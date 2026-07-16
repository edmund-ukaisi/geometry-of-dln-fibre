<task>
Two exact real-analysis convergence questions. Derive each from first principles
(codimension of the singular locus, transverse vanishing order of the determinant,
and the r^{-p} local-integrability criterion in R^d). Exact algebra only; treat any
numerics as a guide, not a proof.

Fix integers a >= 1, b >= 1. Let S be a fixed real n x p matrix of rank rho, and fix T > 0.
Define the "front charge"
    Ch(S) = integral over A in [-T,T]^{b x n} of  det( (A S)(A S)^T )^{-a/2}  dA,
where A is b x n, so A S is b x p and the Gram (A S)(A S)^T is b x b (symmetric PSD).
Assume b <= rho (otherwise the Gram is identically singular).

QUESTION 1. Give the EXACT convergence threshold of Ch(S) for fixed generic S, as an
inequality among (a, b, rho). In particular decide the BOUNDARY case rho = a + b - 1:
does Ch(S) converge or diverge there? Be explicit about strict vs non-strict and the
log-divergent endpoint. Address this subtlety: A is b x n with possibly n > rho, so A has
b(n-rho) "free" directions that map into ker(S) and do not affect A S. Do those free
directions change the effective codimension / threshold, given the integration domain is a
BOUNDED box (not all of R^{b x n})? Concrete instance to settle: b=2, a=2, rho=3 (so
a+b = rho+1), S = 3x3 identity, A in [-1,1]^{2x3}: is
    integral of det( (A S)(A S)^T )^{-1} dA  finite?

QUESTION 2. Now let S ALSO vary over a box, and add an independent loss factor. Define
    I = integral over (Delta, A, S) each in its own box of
        det( (A S)(A S)^T )^{-a/2}  *  frobSq(Delta S)^{-c'}  d(Delta) dA dS,
where Delta is m x n, frobSq(X) = sum of squares of entries of X, and c' > 0 is small
enough that the Delta-integral converges for generic S. Note A appears ONLY in the first
factor and Delta appears ONLY in the second; both couple to S. At the boundary rho = a+b-1
(taking dimensions so generic S in its box has rank rho), is I finite or +infinity?
Determine whether integrating S over a box, or the loss factor frobSq(Delta S)^{-c'},
can "rescue" finiteness of I even if Ch(S) diverges for each fixed generic S. Name the
mechanism (Fubini/Tonelli factorization? correlation between the two factors through S?
change of the effective codimension when S is free?) that decides it.
</task>

<output_contract>
1. Q1 threshold: one clean inequality in (a,b,rho) for convergence, with the derivation
   (codim of {rank(A S) < b}; transverse vanishing order of det(Gram); the R^d radial
   criterion). State the rho = a+b-1 verdict (converge / diverge / log-divergent endpoint)
   and answer the b=2,a=2,rho=3 instance with the exact reason.
2. The free-direction (n > rho) verdict: do they shift the threshold? one sentence + why.
3. Q2 verdict at the boundary: I finite or +infinity, with the decisive mechanism named.
   If finite, name the exact regularizer; if +infinity, give the one-line proof.
4. Flag explicitly which statements are exact derivations vs heuristic.
Keep it tight. No code unless a 3-line sketch clarifies the transverse model.
</output_contract>

<grounding_rules>
Do not assume a conclusion I have not stated; I am withholding my own answer on purpose.
Derive independently. If a step is heuristic (e.g. a genericity or density-boundedness
assumption), say so explicitly and state what would make it rigorous. Distinguish the
fixed-S question (Q1) from the S-varying question (Q2) carefully — they may have different
answers.
</grounding_rules>
