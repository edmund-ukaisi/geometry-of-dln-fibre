<task>
Independent adjudication of a combinatorial reduction for a matrix-integral RLCT proof.
Adjudicate EITHER direction; do not assume a target answer.

SETUP (self-contained). A "chain" is a tuple of positive integer widths M=(M_0,M_1,...,M_L),
L>=2 widths meaning L-1 matrices A_i of shape M_{i+1} x M_i whose product is P=A_{L-1}...A_0.
We study finiteness of a box integral I(M,c) = ∫_{box} frobSq(P)^{-c} over all factors in a
cube [-T,T], for c below a threshold ½·minAdm(M), where minAdm is defined by the exact
layer-peel recursion (this is banked, sorry-free Lean):
    minAdm(n,m) = n*m                                        (2 widths)
    minAdm(M)   = min_{0<=t<=min(M0,M1)} [ (M0-t)(M1-t) + minAdm(t, M2, ..., M_L) ]   (>=3 widths)
The minimizing t is a "binding cut" t*; redChain(t,M) := (t, M2, ..., M_L) has one fewer width.

A proof strategy ("head-split / front-peel route") discharges finiteness of I(M) by peeling
the front block (M0,M1) at a binding cut t* and recursing on redChain(t*,M). Within this peel
the resolution has, for each binding cut t* and each front-rank shell u = t*+j (j>=0):
  - a PIVOT block: an integral over a u x u matrix P and a u x b block, of
    frobSq(P·Q_p + B·Q_b)^{-c''}, where [Q_p ; Q_b] = Q is the GENERIC deep-tail product
    of shape M1 x M_L (product of generic matrices M1xM2, M2xM3, ..., M_{L-1}xM_L),
    with u+b = M1, a = M0-u, b = M1-u.
  - a CORANK block (only for proper shells a,b>=1): an a x b corank-weight integral against
    the deep product, of shape M2 x M_L.

Two candidate finiteness criteria for the head-split route at a cut u (both are established
facts we hand you; you need NOT re-derive them):
  (PIVOT criterion)  The pivot block is finite up to the reduced comparator threshold IFF
       u * rho >= minAdm(redChain(u,M)),  where rho = rank(Q) = min(M1,M2,...,M_L)
       (the generic rank of the deep-tail product; verified exact, an actual rank, not a bound).
  (CORANK criterion) The corank block's cheap single-shell bound converges IFF
       floor >= a+b, where floor = M2 (if L=0, i.e. 3 widths) else min(M1,M_L)-j.
       This bound is known to UNDER-count: the true corank integral is finite even when it fails
       (a co-minimizer argument gives the deep rank >= a+b+1 on the top-dim reduced component,
        valid only at a NONdegenerate binding cut where a=M0-t*>=1 AND b=M1-t*>=1).

There is one exact measure-preserving symmetry: chain REVERSAL. reverse(M) = (M_L,...,M_0),
realized by transposing every factor and reversing their order; frobSq(P)=frobSq(P^T); the map
is a linear bijection of parameter cubes with |det|=1. So I(M,c) = I(reverse(M),c) exactly, and
minAdm(reverse M) = minAdm(M) (reversal is a permutation of widths; minAdm is permutation-invariant).

THE REDUCTION UNDER TEST ("route B"). We can already build the head-split route for chains where
the front seam is non-wide. The proposal: at each recursion node, ORIENT the chain (use M or
reverse(M)) so the chosen front-peel is finite, then recurse. This works iff every nondegenerate
chain (all widths>=1, >=3 widths) has a front-OR-back end whose head-split front-peel is finite.
</task>

<output_contract>
Answer these, each with an explicit verdict + reasoning (concise):

Q1. WHICH criterion is the real divergence boundary for the head-split ROUTE (not the true
    integral I(M), which is finite regardless)? Is it the PIVOT criterion, the CORANK criterion,
    or their union? Justify by the logic of what makes the ROUTE (this specific chart/resolution)
    reach the reduced comparator, versus what makes the true integral finite.

Q2. Does the co-minimizer deep-rank argument (deep rank >= a+b+1 on the top-dim component) RESCUE
    the PIVOT block? Consider a narrow-WAIST chain, e.g. M=(2,1,2) and M=(3,2,3): compute the
    binding cut(s), rho, and u*rho vs minAdm(redChain(u,M)) at the binding cut. State whether the
    co-minimizer applies (its hypothesis a,b>=1) and whether it changes the pivot verdict.

Q3. Does every nondegenerate >=3-width chain have a front-OR-back end whose head-split front-peel
    is finite (under the criterion you chose in Q1)? If YES, give the combinatorial argument.
    If NO, exhibit the smallest counterexample chain (bad from BOTH ends) and characterize the
    family. Consider palindromes and "peak/waist" chains (an interior width < both neighbors).

Q4. Is the reversal change-of-variables I(M)=I(reverse M) sound? Flag any subtlety: the box domain
    symmetry under transpose, frobSq(P) vs frobSq(P^T), the target (here B=0, zero-product locus),
    and whether the Jacobian is genuinely |det|=1.
</output_contract>

<grounding_rules>
- Exact integer arithmetic for minAdm and all cut computations; show the small computations.
- Distinguish FACT (a computation or a cited established result) from INFERENCE (your reasoning).
- Do not assume the reduction holds or fails; adjudicate from the arithmetic.
- If you find the answer hinges on a definition ambiguity (e.g. which shells the route must cover,
  or whether the binding-cut main peel j=0 counts), say so explicitly and give the verdict under
  each reading.
</grounding_rules>
