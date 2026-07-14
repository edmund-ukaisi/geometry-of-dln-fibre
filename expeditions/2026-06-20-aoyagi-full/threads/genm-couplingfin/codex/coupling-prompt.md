<task>
Adjudicate the EXACT convergence threshold (RLCT / Aoyagi-style) of a coupled multi-variable singular
integral that gates a formalisation step. Decide the direction; do NOT assume convergence, and do NOT
assume the threshold equals the "fixed-Q" value below.

SETUP (real matrices). A deep-linear "chain" M = (M0, M1, M2, ..., M_last) of positive-integer widths.
Fix a cut u with 1 <= u <= min(M0,M1); a = M0-u >= 1, b = M1-u >= 1, n = M_last.
The deep product beyond the front layer is
    Z_full = A0 * Z_deep,   A0 : M1 x M2   (a free layer, entries in a box),   Z_deep : M2 x n.
Split A0's rows into u "pivot" rows z0 (u x M2) and b "corank" rows A_cor (b x M2). Then Z_full's rows
split as
    Q_p = z0 * Z_deep   (u x n, "pivot rows"),     Q_b = A_cor * Z_deep   (b x n, "corank rows"),
    Q_stack = [Q_p ; Q_b]   (M1 x n).

THE PIVOT ENERGY (front top-rows). The front layer's top u rows are [P | B12], P: u x u, B12: u x b, over
a box (P near-invertible, |det P| bounded below). The "pivot energy" is
    w(P, B12, A_cor)  =  frobSq( [P | B12] * Q_stack )  =  frobSq( P*Q_p + B12*A_cor*Z_deep ).
Note w DEPENDS on A_cor through the bilinear cross-term B12*A_cor*Z_deep.

THE INTEGRAL / DOMINATION IN QUESTION. In the resolution, the front pivot integral must be dominated by a
reduced comparator whose loss is the A_cor-FREE  decLoss = |v|^2 * frobSq(Q_p)  (a radial coordinate v).
The comparator's convergence threshold is  minAdm(u, M2, ..., M_last)/2  where minAdm is the QIP recursion
    minAdm(len<=1)=0;  minAdm(x,y)=x*y;  minAdm(M)=min over 0<=t<=min(M0,M1) of (M0-t)(M1-t)+minAdm(t,M2,..).
A downstream "shell" restriction is available: one may restrict to  { sigma_min(Z_full) >= eps }  (a fixed
eps>0) -- i.e. Z_full has all its singular values bounded below; the rank-drop region of Z_full is handled
by a SEPARATE deeper branch and is NOT part of this integral.

FACT PROVED ELSEWHERE (verify, do not just accept): for a FIXED generic Z_stack of maximal rank
rho := min(M1, M2, ..., M_last), the map [P|B12] -> [P|B12]*Q_stack is linear of rank u*rho, so the
FIXED-Q integral  int_{[P|B12] box} w^{-c} d[P|B12]  converges iff c < u*rho/2.

QUESTIONS.
Q1 [exact]. Does integrating over A_cor (with the coupling B12*A_cor*Z_deep) as a FREE box variable change
   the small-loss scaling of w? Specifically: is the threshold of
       J_free(c) = int_{[P|B12] box, A_cor box} w^{-c}
   still u*rho/2, or is it LOWER? Analyze via the zero-locus geometry of { [P|B12]*Q_stack = 0 } as A_cor
   varies, paying attention to the sub-locus where the corank rows Q_b enter the row-space of the pivot
   rows Q_p (i.e. A0 = [z0;A_cor] drops rank / Z_full drops rank). Give the exact threshold of J_free for
   the concrete case M=(3,3,3), u=2 (so u=2, a=b=1, M2=n=3, Z_deep=I3, z0 a fixed generic 2x3, A_cor 1x3),
   with justification (dimension/codimension of the degenerate stratum + the standard dist^{-2c} criterion).
Q2 [exact]. Now impose the shell restriction { sigma_min(Z_full) >= eps }. Does the threshold of
       J_shell(c) = int_{[P|B12] box, A_cor box, sigma_min(Z_full)>=eps} w^{-c}
   equal u*rho/2 ? I.e. does the shell exclude exactly the degenerate stratum from Q1? Is the shell
   restriction NECESSARY for the threshold to be u*rho/2 (i.e. is J_free strictly more singular than
   J_shell)? Answer for M=(3,3,3)@u=2 with numbers, and state the general principle.
Q3 [exact]. The A_cor -> 0 limit: as A_cor -> 0, does w -> 0 (a divergence source) or does w stay bounded
   below? Is the pivot-vanishing locus {w=0} DISJOINT from (transverse to) the corank-vanishing locus
   {Q_b=0}? Conclude whether the A_cor->0 direction is a pivot-integral divergence or belongs entirely to
   a separate corank charge.
Q4 [exact]. The finite-constant condition. For a finite C with J_shell(c) <= C * (comparator integral) to
   exist throughout the comparator's convergence range c < minAdm(u,M2,..,M_last)/2, state the exact
   condition on the chain data relating u*rho and minAdm(u,M2,...,M_last). Compute it for M=(3,3,3)@u=2 and
   M=(3,3,4,4)@u=2 (both are binding cuts). In each case say whether a finite C exists, and if it is
   marginal (equality) discuss whether C stays finite as c -> critical or only for c strictly below.
Q5 [inference]. Overall: is the coupled pivot domination BOUNDED (finite C, state the exact scope
   condition on the chain) or is there an UNCONTROLLED direction that no finite C absorbs (state it
   precisely, and whether the shell + a separate corank charge dispose of it)?
</task>

<output_contract>
Five short sections Q1..Q5. For each: verdict + a one/two-line exact justification, tagged [FACT]
(proof/exact dimension-count/convergence exponent) vs [INFERENCE]. State thresholds as exact rationals,
not decimals. For Q1 give the exact threshold of J_free for (3,3,3)@u=2. End Q5 with a single line:
BOUNDED (with the exact scope condition) or WALL (with the exact uncontrolled direction). Be terse.
</output_contract>

<grounding_rules>
- Exact algebra for all load-bearing claims (codimensions, RLCT exponents). Monte-Carlo is a guide only.
- If the "fixed-Q gives u*rho/2" fact is wrong, say so.
- If J_free's threshold is below u*rho/2, give the exact value and the exact degenerate stratum causing it.
- Do NOT assume my conclusion; I have deliberately withheld it. Argue whichever direction is correct.
</grounding_rules>
