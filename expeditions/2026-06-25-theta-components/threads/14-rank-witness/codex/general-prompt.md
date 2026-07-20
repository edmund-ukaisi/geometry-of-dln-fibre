<task>
Independent proof-audit of a GENERAL fibre-Jacobian rank theorem for deep linear networks.
We need to decide whether a per-case-verified rank identity holds for ALL dimension vectors and
ranks, and to pin its exact scope. Derive from first principles; do not rubber-stamp.

SETUP (exact). Fix d=(d_0,...,d_N) of nonneg integers, N arrows, over an INFINITE field k.
Rep_d = affine space of tuples A=(A_1,...,A_N), A_i an (d_i x d_{i-1}) matrix.
  mult(A) = A_N * A_{N-1} * ... * A_1   (a d_N x d_0 matrix).
Fix r, 0 <= r <= min_i d_i. E_r = diag(I_r,0) of shape d_N x d_0, rank exactly r.
  Fib = { A : mult(A) = E_r }   (affine scheme), cut by F_{ij} = (mult(A) - E_r)_{ij} = 0.
Fibre Jacobian at A: J(A), the matrix of  Adot |-> sum_i L_i Adot_i R_i,
  L_i = A_N..A_{i+1}  (d_N x d_i),   R_i = A_{i-1}..A_1  (d_{i-1} x d_0).

ESTABLISHED FACTS (exact, proved earlier in the project; you may USE these):
- delta := r*(d_0 + d_N - r) is the determinantal codim of the rank-<=r locus Sigma^{<=r} at E_r.
- dsh := sorted-ascending of (d_0-r,...,d_N-r). C_sh := the combinatorial codim of the SHIFTED
  zero-product variety {B : B_N..B_1 = 0} on dim vector dsh (a closed form C = cValue(dsh)).
  Q := delta + C_sh is the fibre codimension (= "C + delta"), proved separately.
- theta := number of top-dimensional irreducible components of Fib = C(m, |qdelta|) where
  (m, qdelta) are the QIP data of dsh. The top components biject with corner-r Kostant partitions
  of dsh.
- For any A in Fib: U_i := (A_i..A_1)(k^r) is r-dimensional; A_i : U_{i-1} -> U_i is iso; the
  quotient maps Abar_i : k^{d_{i-1}}/U_{i-1} -> k^{d_i}/U_i satisfy Abar_N..Abar_1 = 0
  (the "shifted" rep is a zero-product rep on the quotient dim vector (d_i - r)).

VERIFIED ON 6 CASES (exact rank over Q, plus a complete 9x9-minor enumeration on one):
  (2,2,2)r1 Q=4 th=2; (2,2,2,2)r1 Q=4 th=3; (3,3,3)r2 Q=9 th=2; (2,2,2,2,2)r0 Q=3 th=6;
  (3,3,3)r1 Q=8 th=1; (3,2,3)r1 Q=7 th=2.
On every TOP component the generic rank of J equals Q = delta + C_sh.

THE RANK-SPLIT CLAIM TO AUDIT (conjectured general, proved per-case):
  rank J(A) = delta + dim I(Abar),   where
  I(Abar) := sum_i  im(Lbar_i) tensor Ann ker(Rbar_i)   inside Hom(k^{d0}/U_0, k^{dN}/U_N),
  Lbar_i = Abar_N..Abar_{i+1}, Rbar_i = Abar_{i-1}..Abar_1 (the quotient partials), and on the
  dense orbit of EVERY top Kostant component  dim I(Abar) = C_sh, giving rank J = Q generically.

QUESTIONS (answer each; mark every claim PROVEN / CONJECTURE / GAP):

Q1. THE SPLIT delta + dim I(Abar). Is the decomposition rank J(A) = delta + dim I(Abar) valid for
    EVERY A in Fib and every (d, r) (infinite field)? Give the exact argument: the change of basis
    aligning U_i (the through-flag) so J becomes block-triangular, the proof that the endpoint block
    contributes EXACTLY delta = r(d_0+d_N-r) (not less -- mind that the r-image and r-source blocks
    overlap; is delta the right count or is there a correction r^2?), and that the complementary
    block is exactly the shifted zero-product differential. Where, if anywhere, does the split need
    A to be GENERIC rather than arbitrary in Fib?

Q2. dim I(Abar) = C_sh ON THE GENERIC TOP STRATUM. This is the crux. For a zero-product rep
    Abar_N..Abar_1 = 0 on dim vector dsh, lying on the dense orbit of a top Kostant component, is
    dim(sum_i im(Lbar_i) tensor Ann ker(Rbar_i)) ALWAYS equal to C_sh? Is this a known theorem
    (the tangent space to the zero-product variety / the smoothness of the open orbit in each
    top component)? Give the cleanest proof or name the obstruction. In particular: is the generic
    zero-product top stratum a SMOOTH point of its component (so tangent dim = component dim,
    forcing rank = codim)? Cite the mechanism (Kostant / quiver-orbit smoothness / Ext^1 vanishing).

Q3. PER-COMPONENT vs GLOBAL minor, sharp dividing line. Verified: theta=1 (qdelta=0) admits a
    single global Q-minor; theta>=2 forces per-component minors (disjoint active arrow-intervals).
    PROVE the dividing line: theta = 1 IFF a single fixed coordinate Q-minor of J is nonvanishing
    on the entire generic locus. Is "theta=1" equivalent to "the Jacobian matroids of all top
    components share a common basis"? Does r saturating to a complete intersection (Q = d_N d_0)
    change this (it should NOT -- (2,2,2)r1 has Q=4=d_N d_0 yet theta=2 and per-component)?

Q4. KILL-PROBES. Identify the SMALLEST (d, r) most likely to BREAK rank J = delta + C_sh on some
    top component -- e.g. asymmetric endpoints (d_0 != d_N), an internal node strictly smaller than
    endpoints (a "valley", so a quotient node has dim 0 forcing a forced rank drop), wide m>=3 with
    |qdelta|>=2, or non-equidimensional fibres (top components of different dims). Name 2-3 such
    cases and predict, for each, whether the split survives and why.

OUTPUT CONTRACT:
- A short answer to each of Q1-Q4, each claim tagged PROVEN / CONJECTURE / GAP.
- For Q1: explicitly resolve whether the endpoint block is delta or delta - (something).
- For Q2: state whether this is a citable theorem and give its name/scope, or flag it as the gap.
- For Q3: a crisp iff or a counterexample.
- For Q4: 2-3 concrete kill-probe (d,r) with predictions.

GROUNDING RULES:
- Reason from exact algebra (product-rule differential, the through-flag block decomposition,
  ranks of Lbar_i/Rbar_i, quiver-orbit tangent spaces). Numeric rank only guides.
- Distinguish "tangent space dim = codim" (smoothness) from "rank = codim" carefully.
- If Q2 reduces to a known smoothness/normality statement about zero-product (nilpotent-type)
  quiver loci, NAME it precisely with its hypotheses. If it is genuinely open, say so.
- Do NOT assume the conclusion. If a step needs genericity or a Kostant hypothesis, say exactly which.
</task>
