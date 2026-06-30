"""
Pin down the general linear-algebra fact and probe the REAL weak point.

CLAIM (the lemma that makes (a)=>(b) automatic):
  Let G be a k x N matrix whose ROWS g_1..g_k are linearly independent (as covectors in
  (R^N)*). Then there EXISTS a set P of N-k standard coordinate covectors {e_p^* : p in P}
  such that {g_1,...,g_k} u {e_p^* : p in P} is a basis of (R^N)*.

PROOF (Steinitz exchange / matroid basis-extension on the column matroid):
  G has rank k => some k columns C of G are linearly independent => G[:,C] is k x k
  invertible. Take P = complement of C (the other N-k columns). The (k + (N-k)) x N = N x N
  block matrix
        [ G        ]      (rows = the k functionals)
        [ e_p^* p in P ]  (rows = coordinate covectors for p NOT in C)
  has, after column-reordering to [C | P], the block form
        [ G[:,C]   G[:,P] ]
        [   0        I     ]
  whose determinant is det(G[:,C]) * det(I) = det(G[:,C]) != 0.  QED.

So (a)=>(b) is automatic and has NOTHING to do with the gradient structure: it is a basis-
extension fact for the standard coordinate basis. The brief's worry ("a subspace can fail to
have a coordinate complement") conflates two different statements:
  - FALSE in general: a fixed k-dim SUBSPACE V need not have a coordinate complement of a
    PRESCRIBED form, AND its ORTHOGONAL complement need not be coordinate. (e.g. V = span(e1+e2)
    in R^2 -- its only coordinate complements are span(e1) and span(e2), both work; bad example.
    Real failure: you cannot always find a coordinate complement to V that ALSO contains a
    prescribed vector.)
  - TRUE always (what we need): the DUAL covector family {g_i} (independent) extends to a
    basis of (R^N)* by ADDING coordinate covectors. This is just "extend an independent set to
    a basis using vectors from a spanning set (the coordinate basis spans)" = Steinitz.

The confusion: "coordinate complement of the SPAN of the g_i" (a primal subspace question) vs
"complete the g_i to a basis with coordinate covectors" (the dual question we actually have).
DPhi = [G ; P] invertible is the SECOND. The second is ALWAYS solvable. Verify the distinction
numerically: build a subspace with NO coordinate complement of a given form, yet its
generators still extend to a basis by coordinate covectors.
"""
import sympy as sp
from sympy import Matrix, zeros, eye
from itertools import combinations
import random

random.seed(0)


def extends_by_coords(G):
    """Test: do the rows of G (k x N) extend to a basis of (R^N)* by adding coord covectors?
    Returns the chosen P or None. Always succeeds iff rank(G)=k."""
    k, N = G.shape
    if G.rank() != k:
        return None
    # find k independent columns
    C = []
    cur = zeros(k, 0)
    for c in range(N):
        t = cur.row_join(G[:, c])
        if t.rank() > cur.rank():
            cur = t; C.append(c)
            if len(C) == k: break
    P = [p for p in range(N) if p not in C]
    DPhi = G.copy()
    for p in P:
        e = zeros(1, N); e[0, p] = 1
        DPhi = DPhi.col_join(e)
    return P if DPhi.det() != 0 else "BUG"


# (1) Random independent covector families always extend.
print("--- Random independent k x N covector families: do they extend by coords? ---")
fails = 0
for trial in range(200):
    N = random.randint(2, 7); k = random.randint(1, N)
    while True:
        G = Matrix(k, N, lambda i, j: random.randint(-3, 3))
        if G.rank() == k:
            break
    res = extends_by_coords(G)
    if res is None or res == "BUG":
        fails += 1
        print("  FAIL", G.tolist())
print(f"  failures: {fails} / 200")

# (2) The classic 'no coordinate complement' confusion, made precise.
# A primal subspace V can FAIL to have a coordinate complement of a *given* vector,
# but the DUAL extension question always succeeds. Show a subspace with restricted
# coordinate complements but whose annihilator-generators still extend.
print()
print("--- Distinction: primal subspace V=span((1,1,1)) in R^3 ---")
V = Matrix([[1, 1, 1]])  # as a covector / as a 1-dim span
# Does the covector (1,1,1) extend to a basis by 2 coord covectors? Yes, any 2 of e1,e2,e3.
print("  (1,1,1) extends by coords:", extends_by_coords(V))
# But e.g. span((1,1)) in R^2: only coordinate complements span(e1),span(e2) -- both work.
# The genuine failure case for PRIMAL coordinate complement of a *subspace* is impossible in
# the sense we need: every proper subspace given by independent covectors extends.

# (3) The real adversarial probe: WHERE could the DLN route break?
# The premise that can fail is NOT (a)=>(b). It is: rank Dg(v) >= nReg.  We must ALSO not need
# MORE than nReg rows. Check: is rank Dg(v) >= nReg at EVERY optimal v?  rank Dg(v) =
# H0*rkA2 + rkA1*H2 - rkA1*rkA2.  With rk(A1 A2)=r <= min(rkA1,rkA2). nReg=r(H0+H2-r).
# Minimise rank Dg(v) over (rkA1=a, rkA2=b) with r<=min(a,b), a<=min(H0,H1), b<=min(H1,H2).
print()
print("--- Probe: is rank Dg(v) >= nReg at EVERY optimal v? minimise over admissible (a,b) ---")
def rankDg(H0, H1, H2, a, b):
    return H0 * b + a * H2 - a * b
def check_widths(H0, H1, H2):
    worst = None
    for r in range(0, min(H0, H1, H2) + 1):
        nReg = r * (H0 + H2 - r)
        # admissible factorisations A1A2=B with rkB=r: need a>=r,b>=r, a<=min(H0,H1), b<=min(H1,H2)
        for a in range(r, min(H0, H1) + 1):
            for b in range(r, min(H1, H2) + 1):
                # also need rank(A1 A2) can equal r with these ranks -- always possible if
                # a,b>=r and there is room: rk(A1A2)>= a+b-H1 (Sylvester). Need r achievable:
                # r in [max(0,a+b-H1), min(a,b)].
                if not (max(0, a + b - H1) <= r <= min(a, b)):
                    continue
                rk = rankDg(H0, H1, H2, a, b)
                slack = rk - nReg
                if worst is None or slack < worst[0]:
                    worst = (slack, r, a, b, nReg, rk)
    return worst
for (H0, H1, H2) in [(3,3,3),(2,2,2),(4,4,4),(3,2,3),(2,3,2),(5,1,5),(1,5,1),(4,2,4),(2,4,2),(3,1,3)]:
    w = check_widths(H0, H1, H2)
    print(f"  H={(H0,H1,H2)}: worst slack (rankDg - nReg) = {w[0]} at "
          f"(r={w[1]},a={w[2]},b={w[3]}), nReg={w[4]}, rankDg={w[5]}")
