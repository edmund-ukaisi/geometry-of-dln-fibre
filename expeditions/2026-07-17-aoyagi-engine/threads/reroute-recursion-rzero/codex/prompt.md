<task>
Adjudicate a KILL-CONDITION for a real-log-canonical-threshold (RLCT) computation in
Watanabe singular learning theory, via resolution of singularities. Decide ONE sharp
truth-value with exact algebra: does resolving a residual locus introduce a divisor whose
RLCT-ratio is STRICTLY LESS than a claimed minimum?
</task>

<setup>
Deep linear network core loss at the origin: F = || C_1 C_2 ... C_L ||^2 (Frobenius), each
C_i a real matrix of shape M_i x M_{i+1}, evaluated near C_i = 0 (the deepest point). The
dimension vector is M = (M_1, ..., M_{L+1}).

Aoyagi (2023) resolves F by a DEPTH-RECURSION: peel layer 1 (block-eliminate C_1 at
rank t_1 via unipotent, det-1 transforms; radial-blow-up), giving in each chart
    F = (peel monomial)^2 * F',    F' = || X C_3 ... C_L ||^2
a FRESH depth-(L-1) core with widths (t_1, M_3, ..., M_{L+1}). Recurse on F'.

Each terminal chart yields F o g = b_1^2 * U with U(0) != 0 (a "kept rank-survivor" gives the
nonzero constant), b_1 a squarefree monomial in exceptional coords (so the loss vanishes to
order exactly 2 along each exceptional divisor: k=1), and Jacobian |det Dg| a monomial. The
RLCT-ratio of divisor {u=0} is (h+1)/(2k) with h the Jacobian order; the RLCT is the min over
divisors of these ratios.

Combinatorial invariant: for a branch (rank profile) t=(t_1,...,t_L), t_L=0,
t_j <= min(t_{j-1}, M_{j+1}):
    Mval(t) = (M_1-t_1)(M_2-t_1) + sum_{j=2}^{L} (t_{j-1}-t_j)(M_{j+1}-t_j)   [= codim of the
    branch's degeneration locus S(t)].
    minAdm(M) = min_t Mval(t)   (a nested min-recursion; = min codim = the claimed 2*RLCT).

FACT (algebraic identity, machine-verified over many M): for every branch,
    Mval(t_1, s) = (M_1-t_1)(M_2-t_1) + Mval_sub(s),
where Mval_sub is the depth-(L-1) invariant of widths (t_1, M_3,...) and s the sub-branch.
</setup>

<facts_established>
1. Termination: depth strictly decreases each peel (L -> L-1 -> ... -> 1); at L=1, ||C||^2 is
   a nondegenerate (Morse) quadratic, resolved by one blow-up. So the residual recursion halts.
2. Instance (3,3,3,2,2), t=(2,2,1,0), minAdm=4, claimed RLCT=2. A leaf has
   F o g = (w y)^2 * R with R = ||Y_row0||^2 + d2^2||Y_row1||^2 + d1^2||Y_row2||^2, Y=C3bar*C4bar,
   R(origin)=1. The residual locus {R=0}:
   - GENERIC point of {R=0}: codim 4; R is a rank-4 nondegenerate (Morse) quadratic there;
     blowing it up gives k=1, Jacobian order h=3, ratio (3+1)/2 = 2 = minAdm/2 EXACTLY (exact,
     sympy Hessian rank = 4).
   - Deeper coupled strata (a residual generator like d1*||Y_row2|| also -> 0): the local model is
     R_local = xi1^2 + xi2^2 + d2^2 + (d1*mu)^2 (mu a residual coordinate). By RLCT additivity over
     disjoint variable groups, rlct(R_local) = rlct(2 squares) + rlct(1 square) + rlct((d1 mu)^2)
     = 1 + 1/2 + 1/2 = 2. The coupled x^2 y^2 term contributes rlct 1/2, made up to 2 by the
     kept-survivor clean squares.
3. Certified coupled case (3,3,4), t=(1,0): peel codim (3-1)^2=4, base 1*4=4, Mval=8. The peel
   divisor {q=0} and residual divisor {u=0} are JOINED by the forced corner blow-up {q=u=0};
   the join divisor E has Jacobian order h = 3+3+1 = 7 = Mval-1, k=1, ratio (7+1)/2 = 4 = minAdm/2.
</facts_established>

<questions>
Q1. In the depth-recursion, is the RLCT-ratio of a deep divisor (from resolving the residual
    F'=0), when it lies over the ORIGINAL origin (all C_i=0), necessarily = (1/2)*Mval(full branch)
    rather than (1/2)*Mval_sub(sub-branch)? I.e., is the peel-codim contribution (M_1-t_1)(M_2-t_1)
    ALWAYS added to a deep divisor over the origin? Give the precise geometric reason (or a
    counterexample).
Q2. Can the k=1 property FAIL at a coupled deep stratum -- i.e., can the pulled-back loss vanish to
    order 2k with k>=2 along a single exceptional divisor, dropping (h+1)/(2k) below minAdm/2? The
    coupled term x^2 y^2 has rlct 1/2 (multiplicity 2) -- does that halving ever propagate to make a
    ratio < minAdm/2, or is it always compensated by the kept-survivor / the Jacobian?
Q3. Is there any M and branch where the residual recursion produces a divisor with RLCT-ratio
    STRICTLY LESS than (1/2)*minAdm(M)? Equivalently: is minAdm(M) really the min over ALL divisors
    of the FULL resolution (shallow AND deep), or can a deep divisor undercut it?
Q4. Standard-theory check: for loss = m^2 * G with m a monomial in variables disjoint from G's, is
    rlct(m^2 * G) determined so that no divisor of the G-resolution can have ratio below rlct(G)?
    State the exact relationship (this controls whether the (w y)^2 prefactor can lower a deep ratio).
</questions>

<output_contract>
For EACH of Q1-Q4: a direct verdict (YES/NO/CONDITIONAL) + the exact-algebra reason. If you claim
a mechanism, name it and give the divisor bookkeeping (loss order k, Jacobian order h, ratio). If
you see a genuine counterexample or a gap where a deep ratio < minAdm/2, EXHIBIT it concretely
(specific M, branch, chart). Separate PROVEN from INFERENCE. End with: does the recursion-on-{R=0}
introduce any divisor undercutting minAdm/2 -- WITNESS (no undercut) or OBSTRUCTION (a kill)?
</output_contract>

<grounding_rules>
Use exact algebra only (rationals/symbolic). RLCT conventions are Watanabe's (learning coefficient
lambda; for monomial ideal loss, lambda = min_i (h_i+1)/(2 k_i)). Do NOT rubber-stamp; if the
additive-accumulation-over-the-origin claim (Q1) has a hole, find it. Preserve the
PROVEN-vs-INFERENCE distinction in your answer.
</grounding_rules>
