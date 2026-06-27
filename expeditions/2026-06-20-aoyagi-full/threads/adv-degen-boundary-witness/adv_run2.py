import sympy as sp
from sympy import Rational as Q
from adv_dln import nReg, jacobian_rank_at_deepest, full_hessian_rank, build_chain_symbols, product, report

# ---------------------------------------------------------------------------
# ATTACK on the SINGLE-ORBIT claim: try DIFFERENT deepest points (not the aligned rect-identity).
# The Jacobian J of the product wrt C_k has image  L_k * (R_k^T  kron rows) ... governed by
#   col-space(L_k) and row-space(R_k) where L_k = C_1..C_{k-1}, R_k = C_{k+1}..C_L.
# rank(J) = dim span over k of { L_k E R_k : E arbitrary H_k x H_{k+1} } as matrices in R^{H0 x HL}.
# This is the tangent space to the variety {products}. If a factorization is "non-generic"
# (a factor itself rank-deficient beyond the bottleneck), prefix/suffix ranks could drop -> rank(J) drops.
#
# Build a base point manually for (3,2,3) r=2 where the MIDDLE matrix C2 (2x3) and C1(3x2) are chosen so
# the product is rank 2 but the intermediate width-2 'channel' is used non-generically.
# Actually width at interior = 2 = r here (M_1 = 0): the bottleneck. The product MUST be rank<=2.
# Try a base where C1's columns are NOT independent in the way aligned assumes.
# ---------------------------------------------------------------------------

def manual_report(label, H, r, base, B):
    rk, nv, Jac0, mats = jacobian_rank_at_deepest(H, base)
    nr = nReg(H, r)
    P0 = product(mats)
    P0 = P0.subs({s: 0 for row in mats for s in row.free_symbols})
    prk = sp.Matrix(P0).rank()
    okB = (sp.Matrix(P0) - B) == sp.zeros(B.rows, B.cols)
    print(f"{label}")
    print(f"   H={H} r={r} nReg={nr} ambient={nv} | rank(J)={rk} | prod-rank={prk} | P==B:{okB} | match nReg:{rk==nr}")
    if not okB:
        print(f"   *** base is NOT a deepest point (P != B): not a valid test ***")
    print(f"   flat = {nv-rk}")
    return rk, nr, okB

print("="*72)
print("ATTACK A — alternative deepest factorizations for (3,2,3) r=2 (bottleneck width-2 interior)")
print("="*72)
H=(3,2,3); r=2; B = sp.Matrix([[1,0,0],[0,1,0],[0,0,0]])  # rank-2 target
# Aligned: C1=[[1,0],[0,1],[0,0]], C2=[[1,0,0],[0,1,0]]
base_aligned = [sp.Matrix([[1,0],[0,1],[0,0]]), sp.Matrix([[1,0,0],[0,1,0]])]
manual_report("[A1] aligned C1=[[1,0],[0,1],[0,0]] C2=[[1,0,0],[0,1,0]]", H, r, base_aligned, B)

# Twisted but still rank-2 product = B: C1 with a generic invertible 2x2 top block + extra row, C2 inverse-ish.
# C1 = [[1,1],[0,1],[1,2]], need C1 C2 = B. Let C1top = [[1,1],[0,1]] (rows0,1), invertible. C2 = C1top^{-1}*[[1,0,0],[0,1,0]]
C1t = sp.Matrix([[1,1],[0,1]]); C1 = sp.Matrix([[1,1],[0,1],[1,2]])
C2 = C1t.inv() * sp.Matrix([[1,0,0],[0,1,0]])
manual_report("[A2] twisted C1=[[1,1],[0,1],[1,2]] C2=C1t^-1 [[I2|0]]", H, r, [C1, C2], B)

# A base where C1 has a ZERO row interacting (still product=B). C1=[[1,0],[0,1],[0,0]], C2 chosen.
# Try C2 = [[1,0,5],[0,1,7]] -> product top-left I2, last col of B becomes [5,7,0] != 0. Adjust B.
C1 = sp.Matrix([[1,0],[0,1],[0,0]]); C2 = sp.Matrix([[1,0,5],[0,1,7]])
Bp = C1*C2
manual_report("[A3] C2 with nonzero 3rd col, B = product (rank2)", H, r, [C1, C2], Bp)

print()
print("="*72)
print("ATTACK B — DEGENERATE base point where a FACTOR is rank-deficient (rank < r through a WIDE layer)")
print("="*72)
# (4,2,4) r=2, M=(2,0,2). Interior width = 2 = r (bottleneck). Both factors C1(4x2),C2(2x4) must be rank 2
#   for product rank 2. What if we force C1 rank 1? Then product rank<=1 != 2: NOT a deepest for rank-2 B.
#   So at the boundary the factors adjacent to the bottleneck are FORCED full-rank. (structural fact!)
# Probe: (5,3,2,4) r=2 PARTIAL. The width-3 interior (M=1) is NOT a bottleneck. Can a deepest point have the
#   width-3 'channel' used at rank < 3 but >= 2? Let prefix product C1 (5x3) be rank 2 only (deficient).
H=(5,3,2,4); r=2
# Build base: C2 is (3x2), C3 is (2x4). The bottleneck is at width-2 (position 2, between C2 and C3).
# C1: 5x3, C2: 3x2, C3: 2x4. Make C1 rank 2 (deficient!) so the 'width-3 channel' only carries rank 2.
# Then choose C2,C3 so product = some rank-2 B.
C1 = sp.Matrix([[1,0,0],[0,1,0],[0,0,0],[0,0,0],[0,0,0]])   # 5x3, rank 2 (third col zero) -> DEFICIENT
C2 = sp.Matrix([[1,0],[0,1],[0,0]])                          # 3x2
C3 = sp.Matrix([[1,0,0,0],[0,1,0,0]])                        # 2x4
B = C1*C2*C3
manual_report("[B1] (5,3,2,4) r=2, C1 RANK-DEFICIENT (rank2 not 3) through the wide width-3 layer", H, r, [C1,C2,C3], B)
# Compare to the aligned (C1 full rank 3):
C1f = sp.Matrix([[1,0,0],[0,1,0],[0,0,1],[0,0,0],[0,0,0]])
Bf = C1f*C2*C3
manual_report("[B2] (5,3,2,4) r=2, C1 FULL rank 3 (aligned-ish)", H, r, [C1f,C2,C3], Bf)
