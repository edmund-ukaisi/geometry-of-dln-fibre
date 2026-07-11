<task>
Compute a determinantal codimension for a PRODUCT of matrices, and relate it to a recursive "layer
minimum". Exact algebra; give exact integers and the general formula if you can.

SETUP. Real matrices. A tail chain of widths (M_1, M_2, ..., M_L); factors A_i of size M_i x M_{i+1}
(i=1..L-1); the tail product P = A_1 A_2 ... A_{L-1} is M_1 x M_L. Let (A_1,...,A_{L-1}) range over
the full Euclidean parameter space (dim = Σ_i M_i M_{i+1}).

Define the "layer-min" function on any width chain (m_0,...,m_k):
   mu(m_0, m_1) = m_0 m_1
   mu(m_0,...,m_k) = min_{0<=t<=min(m_0,m_1)} [ (m_0 - t)(m_1 - t) + mu(t, m_2, ..., m_k) ]   (k>=2)
(This mu is the codimension of the zero-product locus {A_1...A_{k-1} = 0} of a chain — assume that.)

QUESTIONS.
 1. For the tail chain (3,3,4) (so A_1 is 3x3, A_2 is 3x4, P = A_1 A_2 is 3x4, ambient dim 21),
    compute the codimension of  V_s = { (A_1,A_2) : rank(A_1 A_2) <= s }  for s = 0, 1, 2, in the
    (A_1,A_2) parameter space. Give the codim of the LOWEST-codimension (dominant) irreducible
    component — this is what a tube volume sees. Do it by dimension count over the irreducible
    components (include {rank A_1 <= s}, {rank A_2 <= s}, and the "geometric" component where neither
    factor drops rank but the composition does).
 2. Compare each to (a) the FREE-matrix determinantal codim (M_1 - s)(M_L - s) = (3-s)(4-s), and
    (b) mu of the reduced tail (M_1 - s, M_2 - s, M_3 - s) = mu(3-s, 3-s, 4-s). Which does the product
    codim equal? State the general conjecture: codim{rank(A_1...A_{L-1}) <= s} = mu(M_1-s,...,M_L-s)?
 3. TUBE EXPONENT vs CODIM. Let σ_q(P) be the q-th singular value (q = s+1). Is the small-ball
    measure{(A_1,A_2) : σ_q(P) <= t} ~ C t^{codim(V_s)} (so the tube exponent EQUALS the codim), or
    can there be a strictly SMALLER exponent (a higher-multiplicity / multiscale rank stratum where
    σ_q vanishes to order >1 in the distance, inflating the tube), and/or a log factor? This matters:
    a smaller exponent would shrink the effective codim.
 4. Given the front-peel identity  minAdm(M_0, M_1,...,M_L) = min_{j>=0} [ M_0 * j + mu(M_1-j,...,M_L-j) ]
    (assume this holds), and the identity of Q2, is the inequality
        minAdm(M_0,...,M_L)  <=  codim{rank(tail product) <= q-1}  +  M_0 (q-1)
    automatically true for every q? If so, why (which term of the front-peel min is it)?
</task>

<output_contract>
Q1: codim(V_s) for s=0,1,2 as exact integers, with the dominant component identified. Q2: which
formula the product codim matches [free / mu-reduced], + the general conjecture with a one-line
justification or counter. Q3: tube-exponent = codim yes/no, with the multiplicity/log caveat stated
exactly. Q4: yes/no + which front-peel term. Mark [exact]/[heuristic].
</output_contract>

<grounding_rules>
- codim of {rank <= s} of a FREE m x n matrix is (m-s)(n-s); dim of rank-exactly-a m x n matrices is
  a(m+n-a).
- For the geometric component, count: choose rank of each factor + the incidence im(A_2) ∩ ker(A_1).
- σ_q(P) ≍ dist(P, {rank ≤ q-1}) for a FREE P; for a product the relevant distance is in
  parameter space — reason about whether σ_q vanishes linearly or to higher order along the dominant
  component.
- Keep "codimension" (an integer) separate from "tube exponent" (a real, possibly with log/multiplicity).
</grounding_rules>
