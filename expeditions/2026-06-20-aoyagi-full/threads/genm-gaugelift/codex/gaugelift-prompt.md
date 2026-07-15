<task>
I am pinning the exponent bookkeeping for one peel step of an RLCT (real log-canonical
threshold) computation for deep linear networks, and I need an independent check of ONE
geometric-codimension question. Please reason from scratch and argue whichever way the
mathematics actually goes — do not try to agree with me.

SETUP (a "peel" of a matrix-chain loss).
A chain of widths M = (M0, M1, M2, ..., M_last) (L+1 widths, L>=1). Fix a "cut" rank
u with 0 <= u <= min(M0,M1). Set a = M0-u, b = M1-u (the "corner" dims). Let
n := M_last. The deep-tail product is Z := Z_deep, an (M2 x n) matrix that is a PRODUCT
of the tail layer-matrices of the reduced chain (u, M2, ..., M_last); it is generically
of full row rank M2 (assume M2 <= n). Two objects enter the peel:
  Q_p = P_pivot . Z      (u x n),   P_pivot a (u x M2) matrix (the reduced chain's layer-1 factor);
  Q_b = A_cor . Z        (b x n),   A_cor a FREE (b x M2) matrix (the "corner" block).
So Q_p, Q_b BOTH factor through the same deep factor Z, and A_cor is the only NEW free
variable of this peel (P_pivot and Z live in the deeper integral). The peel integral is,
schematically, over (A_cor, a "front" block (P,B,C), and a residual radial variable),
   G = INT_{A_cor} det(Q_b Q_b^T)^{-a/2} . [ INT_front ( E_top + E_tr )^{-q} ],
   E_top = || P.Q_p + B.Q_b ||_F^2,   E_tr = || C . Q_p (I - Pi_b) ||_F^2,
   Pi_b = orthogonal projection onto row(Q_b).
The corner-Gram factor det(Q_b Q_b^T)^{-a/2} with A_cor ranging over a (b x M2) box has
the standard corank/Wishart integrability threshold a < rank(Z) - b + 1, i.e. a + b <= M2
(this uses M2 = rank Z, NOT n).

THE KNOWN L=0 (arity-3) ANSWER. When there are NO deeper layers (Z is trivial, n = M2,
Q_p is a free (u x M2) matrix), a joint blow-up resolution stratifies the (A_cor, front)
locus by two integer ranks: ell = rank of an "incidence" matrix W = Q_p . N (N annihilates
row(Q_b)), and s = rank of a "Y-block" Y = (P;C). Each (ell, s) stratum is a single
normal-crossing cell with an integer normal codimension
   C_{ell,s} = u*b + M0*ell + (M0 - s)*(u - ell - s) + s*(d - ell),    d = M2 - b,
and the stratum contributes a radial integral INT_0^delta r^{C_{ell,s} - 1 - 2q} dr,
finite iff q < C_{ell,s}/2. An exact identity holds (verified): with a*b = (M0-u)(M1-u),
   C_{ell,s} + a*b = (M0 - s)(M1 - s) + s*M2       (the ell-terms cancel identically).

MY QUESTION (the ONLY thing I need adjudicated).
Now L >= 1, so Q_p = P_pivot . Z and Q_b = A_cor . Z are PRODUCTS through the deep factor
Z (M2 x n), and the residual deep integral over (P_pivot, Z) is handled SEPARATELY (it is a
"comparator" whose value is governed by the reduced chain (u, M2, ..., M_last)). Consider
the per-stratum normal codimension of the (A_cor, front) blow-up cells at general L.

Q1. Is the per-stratum codimension C_{ell,s} of the (A_cor, front) cells parametrized by
    M2 (the row-dimension of Z / the corank space in which A_cor lives), or by n = M_last
    (the column-dimension of Z)? Concretely: in the "d = ? - b" of the incidence chart and
    the "s*(d - ell)" term, is d = M2 - b or d = n - b? Give your reasoning about which
    dimension controls the codimension of the (A_cor, front) locus, given that A_cor is a
    free (b x M2) matrix and Z is a fixed full-row-rank (M2 x n) factor (so Q_b = A_cor.Z
    ranges only over a b*M2-dimensional family, not b*n-dimensional).

Q2. Does the deep degeneracy of Q_p = P_pivot . Z (i.e. the locus where Q_p drops rank
    because the DEEP product degenerates) enter the (A_cor, front) per-stratum codimension
    C_{ell,s}, or is it instead carried by the separate deep "comparator" integral over
    (P_pivot, Z)? In other words: is the single top-level blow-up cell's radial exponent a
    POLYNOMIAL in the widths (a naive count like s*M2), or does it already contain the deep
    chain's own recursive minimum (a nested min over sub-strata of the (u,M2,...,M_last)
    chain)? A single monomial/normal-crossing blow-up chart has a polynomial (integer) codim
    by construction; a nested-min value only appears after minimizing over a whole family of
    deeper cells. Which is it for the (A_cor, front) chart?

Q3. Given your answers: for the per-stratum finiteness gate we need C_{ell,s} >= K for a
    target integer K. If C_{ell,s} + a*b = (M0-s)(M1-s) + s*M2 (same identity as L=0, using
    M2), is the map K |-> "min over (ell,s) of C_{ell,s}" governed by M2 or by the full deep
    chain? State whether the naive front minimum min_{0<=s<=u}[(M0-s)(M1-s) + s*M2] - a*b can
    ever be STRICTLY LARGER than the true chain minimum, and if so, what carries the gap
    (front cells, or the deep comparator).
</task>

<output_contract>
- Answer Q1, Q2, Q3 in order. Prefix each atomic claim with [FACT] (a derivation you can
  justify) or [INFERENCE] (a plausible reading). Keep facts and inferences distinct.
- For Q1 give the explicit d (M2 - b or n - b) with a one-line reason.
- For Q2 state plainly: polynomial-per-cell (naive) vs nested-min-per-cell (deep).
- If you cannot determine something from the given data, say so; do not invent.
- Be concise; formulas over prose.
</output_contract>

<grounding_rules>
- The dimension counts are exact-integer geometry; do NOT hand-wave with "generically".
- rank Z = M2 generically (M2 <= n); det(Q_b Q_b^T) = det(A_cor (Z Z^T) A_cor^T), and
  Z Z^T is an (M2 x M2) positive-definite matrix (a bounded unit on the chart), so any
  n-dependence enters only through this bounded unit.
- "codimension of a normal-crossing cell" means the number of coordinate normal directions
  whose vanishing defines the cell — an integer polynomial in the widths, never a min.
</grounding_rules>
