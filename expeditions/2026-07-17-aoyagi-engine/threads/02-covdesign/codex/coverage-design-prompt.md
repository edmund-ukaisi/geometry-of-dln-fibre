<task>
Setting (exact, no ML). Fix integers M = (M^(1), ..., M^(L+1)) ("reduced widths").
Let C^(s) be a free real M^(s) x M^(s+1) matrix (entries are coordinates), and let
F(C) = || C^(1) C^(2) ... C^(L) ||_Frobenius^2, the squared norm of the layer product.
F is a real-analytic function of the sum_s M^(s)M^(s+1) entries, homogeneous of degree 2L,
with an isolated-in-direction singularity along the zero locus {prod_s C^(s) = 0}, whose
deepest point is the origin (all entries 0). We integrate over the box B = [-1,1]^N.

Goal object. We must show: for every c' < (1/2) minAdm(M), the box integral
  I(c') = integral_{B} F(C)^{-c'} dC   is FINITE,
where minAdm(M) is the integer given by the recursion
  minAdm(M0)=0; minAdm(M0,M1)=M0*M1;
  minAdm(M0,M1,...) = min_{0<=t<=min(M0,M1)} [ (M0-t)(M1-t) + minAdm(t, M2, M3, ...) ].
(minAdm(M) equals the minimum, over "admissible" weakly-decreasing rank profiles
 t=(t^(1),...,t^(L)) with t^(L)=0, of Mval(t) = (M0-t1)(M1-t1) + sum_{j>=2}(t_{j-1}-t_j)(M_{j+1}-t_j),
 which is the codimension of the rank-profile stratum. Verified exactly by enumeration.)

Aoyagi's construction (the thing we are reconstructing). She resolves F at the origin by a
recursive blow-up (a DOUBLE induction on (S,J): S the layer index, J the number of cleared
unit pivots). At each node she looks at the equal-run pattern of a monomial vector b (the
accumulated exceptional-coordinate weights) above index J, and BRANCHES:
  - Case 1 (partial run: b_{J+1}=...=b_{J+J1} != b_{J+J1+1}, J1 < remaining): blow up a
    d-sub-block; sub-split 1(1) [d-block divisible by an existing exceptional coord u] vs
    1(2) [introduce a new pivot coordinate u];
  - Case 2 (full run: b_{J+1}=...=b_{M(S)}): blow up the full residual block; new exceptional
    divisor exponent (M(S)-J)(M^(S+1)-J).
Each branch introduces exceptional divisors u_{s,k}; each carries Jacobian power M_{s,k}-1 and
the loss vanishes to order 2 along it, giving that divisor a "ratio" M_{s,k}/2. At S=L+1 the
product is fully diagonal (normal crossings) and the terminal divisors have exponent Mval(t).
The PAPER ASSERTS ("by a blow-up process") that these charts cover and that the minimum ratio
over the family is (1/2)minAdm; it does not prove the family is exhaustive.

What is already established (facts, take as given):
  - The RLCT value at a POINT, given an atlas (a covering chart family that monomialises F),
    equals (1/2)minAdm -- this composition is proven downstream.
  - Every EMITTED branch's terminal divisor exponent = Mval(t) for an admissible profile t, and
    minAdm = inf over admissible t of Mval(t); so every emitted ratio >= (1/2)minAdm by the
    inf property alone (no covering statement needed for THIS inequality).
  - A single blow-up of a smooth center is proper; its affine charts cover a neighborhood of the
    exceptional divisor.
  - At corank >= 2, a "threshold-only" summary (per-row weight multiplicities) is provably wrong;
    the symbolic divisor-support ("which exceptional coords multiply which generator", the diag(b)
    sharing) must be carried -- verified by an exact obstruction (ideal <dx,dy> has rlct 1/2 vs
    <d1 x, d2 y> has rlct 1).

CONSTRAINT (binding): the argument may NOT use "rlct(F) = (1/2)minAdm" anywhere -- that is the
thing being built; using it to rule out a bad divisor is circular. We may use only the geometry
of the blow-ups and the combinatorics of minAdm.

My specific sub-questions:
  (Q1) To prove I(c') < infinity for c' < (1/2)minAdm, what exactly must the chart family satisfy,
       and which part is the genuinely load-bearing NEW content vs. bookkeeping? Decompose it.
  (Q2) WHY does branching on the b-equal-run pattern (Case 1 partial / Case 2 full; then 1(1)/1(2))
       EXHAUST all local configurations -- i.e. why does every point near the origin land in some
       branch's chart? Where does properness/covering enter, per blow-up and globally?
  (Q3) How would you prove "no UNTRACKED exceptional divisor has ratio < (1/2)minAdm" WITHOUT
       using rlct = (1/2)minAdm? What is the right induction (per-blow-up covering lemma + induction,
       vs. one global argument)? What family of candidate divisors must be ruled out?
  (Q4) Where is this design most likely to be WRONG or incomplete? Name the sharpest failure mode
       and the smallest instance that would exhibit it if it exists.
</task>

<output_contract>
  Answer Q1-Q4 in order, each a short tight paragraph. For Q1 give an explicit decomposition
  (list the sufficient conditions on the chart family, marking each "load-bearing new" or
  "bookkeeping"). For Q3 name the induction structure and the candidate-divisor family precisely.
  For Q4 give ONE sharpest failure mode + the smallest concrete (M, branch) that would exhibit it.
  Flag every claim as [proof-sketch you can defend] vs [heuristic/inference]. Do not write Lean.
  Be concrete about the blow-up geometry; avoid generic algebraic-geometry platitudes.
</output_contract>

<grounding_rules>
  Reason from the setup above; do not assume access to Aoyagi's paper. If you need a fact not
  given, state it as an assumption and mark it [assumed]. Distinguish what you can prove from
  what you conjecture. If a sub-question hides a false presupposition, say so. It is acceptable
  and useful to disagree with the framing.
</grounding_rules>
