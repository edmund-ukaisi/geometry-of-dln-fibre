import sympy as sp
from sympy import Rational as Q
from adv_dln import nReg, jacobian_rank_at_deepest, product

def rk_at(H, r, base):
    rk, nv, Jac0, mats = jacobian_rank_at_deepest(H, base)
    P0 = product(mats).subs({s:0 for row in mats for s in row.free_symbols})
    return rk, nv, sp.Matrix(P0)

def show(label, H, r, base, expectB=None):
    rk, nv, P = rk_at(H, r, base)
    nr = nReg(H, r)
    prk = P.rank()
    note = ""
    if expectB is not None:
        note = f" P==B:{(P-expectB)==sp.zeros(*expectB.shape)}"
    flag = "" if rk==nr else "   <<<<<<<<<< MISMATCH! rank(J) != nReg"
    print(f"{label}\n   H={H} r={r} nReg={nr} ambient={nv} rank(J)={rk} prodrank={prk}{note} match:{rk==nr}{flag}")
    return rk, nr

print("="*72)
print("ATTACK C — END-FACTOR rank-deficient (the outer matrices govern the tangent of rank<=r variety)")
print("="*72)
# The tangent to {rank<=r} at B is { U: U = A B0 + B0 D ... } actually span of (col-space extensions) and
# (row-space extensions). The differential image span_k{L_k E R_k}. For k=1 (first factor): L_1 = I,
# image = { E R_1 } = rows in row-space of R_1 = C_2..C_L, scaled into H0 rows. For k=L: R_L=I,
# image = { L_L E } = columns in col-space of L_L = C_1..C_{L-1}.
# So rank(J) needs col-space(C_1..C_{L-1}) AND row-space(C_2..C_L) to be FULL (dim r) AND aligned with B.
# ATTACK: make the SUFFIX C_2..C_L have row-space of dim r but col-space of prefix only dim r... they ARE r.
# The real risk: a factorization where B = L * R with L (H0 x r-ish) and the differential misses directions.

# Construct (4,2,4) r=2 with a base whose FIRST factor C1 (4x2) is fine but spans an unusual 2-dim subspace.
H=(4,2,4); r=2
C1 = sp.Matrix([[1,0],[1,1],[0,1],[0,0]])   # 4x2 rank 2, generic-ish columns
C2 = sp.Matrix([[1,0,2,0],[0,1,0,3]])        # 2x4 rank 2
B = C1*C2
show("[C1] (4,2,4) r=2 generic non-aligned factorization", H, r, [C1,C2], B)

# Now a base where C1 col-space and C2 row-space are 'misaligned' relative to B's natural spaces.
C1 = sp.Matrix([[1,1],[1,1],[0,1],[1,0]]); C2 = sp.Matrix([[2,1,0,1],[0,1,3,1]])
B = C1*C2
show("[C2] (4,2,4) r=2 more generic", H, r, [C1,C2], B)
print()

print("="*72)
print("ATTACK D — the DANGEROUS one: a deepest point that is a CRITICAL/SINGULAR point of the param map")
print("   (a factorization where the differential of mult has a LARGER kernel than the gauge group)")
print("="*72)
# Gauge dim for a chain = sum over interior layers of dim of stabilizer of the bottleneck. For a generic
# rank-r factorization through interior widths H_1..H_{L-1}, the kernel of J (flat dirs) = ambient - rank(J).
# The CLAIM: rank(J) = nReg always. If we find a base with rank(J) < nReg, the flat space is BIGGER and
# rlct < nReg/2 -> LEMMA BROKEN. Hunt: factorizations where an intermediate factor is rank-deficient AND
# adjacent to a NON-bottleneck wide layer so the deficiency is 'allowed' (product still rank r).
H=(3,2,3); r=2  # interior width 2 = r (bottleneck). Both factors forced rank 2. Hard to break.
# Try (3,2,2,3) r=2: M=(1,0,0,1). interior widths 2,2 both = r. two bottlenecks. factors C1(3x2),C2(2x2),C3(2x3)
H=(3,2,2,3); r=2
C1=sp.Matrix([[1,0],[0,1],[0,0]]); C2=sp.Matrix([[1,0],[0,1]]); C3=sp.Matrix([[1,0,0],[0,1,0]])
B=C1*C2*C3
show("[D1] (3,2,2,3) r=2 aligned two bottlenecks", H, r, [C1,C2,C3], B)
# Make the middle C2 a generic invertible 2x2 (still rank 2, product changes but rank 2)
C2b=sp.Matrix([[1,2],[3,7]]); B2=C1*C2b*C3
show("[D2] (3,2,2,3) r=2 middle generic invertible", H, r, [C1,C2b,C3], B2)
# Make C2 SINGULAR (rank 1)! Then product rank <= 1 < 2: not a rank-2 deepest. But test what rank(J) is
#   for the rank-1 product (this is a DIFFERENT r effectively). Skip as invalid for r=2.
print()

print("="*72)
print("ATTACK E — PARTIAL degeneracy r=2 with the bottleneck at an END-adjacent vs deep interior")
print("="*72)
# (2,3,4) r=2: M=(0,1,2). H0=2=r is an END bottleneck (M_0=0). nReg=2*(2+4-2)=8. ambient=2*3+3*4=18.
H=(2,3,4); r=2
C1=sp.Matrix([[1,0,0],[0,1,0]]); C2=sp.Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,0]]); B=C1*C2
show("[E1] (2,3,4) r=2 END bottleneck H0=2=r (M_0=0)", H, r, [C1,C2], B)
# (4,3,2) r=2: M=(2,1,0). H_last=2=r END bottleneck. nReg=2*(4+2-2)=8. ambient=12+6=18.
H=(4,3,2); r=2
C1=sp.Matrix([[1,0,0],[0,1,0],[0,0,1],[0,0,0]]); C2=sp.Matrix([[1,0],[0,1],[0,0]]); B=C1*C2
show("[E2] (4,3,2) r=2 END bottleneck H_last=2=r (M_2=0)", H, r, [C1,C2], B)
