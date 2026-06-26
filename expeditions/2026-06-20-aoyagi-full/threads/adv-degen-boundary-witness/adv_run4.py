import sympy as sp
from sympy import Rational as Q
from adv_dln import nReg, jacobian_rank_at_deepest, product

def analyze(label, H, r, base):
    rk, nv, Jac0, mats = jacobian_rank_at_deepest(H, base)
    nr = nReg(H, r)
    matvals = [M.subs({s:0 for s in M.free_symbols}) for M in mats]
    P = matvals[0]
    for M in matvals[1:]:
        P = P*M
    prk = P.rank()
    # prefix products L_L = C_1..C_{L-1}, suffix R_1 = C_2..C_L
    L = len(H)-1
    LL = matvals[0]
    for M in matvals[1:-1]:
        LL = LL*M
    R1 = matvals[1]
    for M in matvals[2:]:
        R1 = R1*M
    rank_colspace_LL = LL.rank()   # = dim colspace of C_1..C_{L-1}
    rank_rowspace_R1 = R1.rank()   # = dim rowspace of C_2..C_L
    flag = "" if rk==nr else "  <<<<<<<<<<<<<< MISMATCH"
    print(f"{label}")
    print(f"   H={H} r={r} nReg={nr} ambient={nv} rank(J)={rk} prodrank={prk} match:{rk==nr}{flag}")
    print(f"   rank(C_1..C_(L-1))={rank_colspace_LL}  rank(C_2..C_L)={rank_rowspace_R1}  (both should be r={r} for surjectivity)")
    return rk, nr

print("="*72)
print("ATTACK F — can the prefix/suffix product exceed rank r? (no bottleneck in 1..L-1)")
print("="*72)
# (3,4,1,4,3) r=1: M=(2,3,0,3,2). ONLY bottleneck at the MIDDLE width-1 (position 2). The prefix C1 (3x4)
#   and C1 C2... let's see. Actually bottleneck at interior width-1 forces product rank<=1=r. But the
#   prefix C_1..C_{L-1} = C1 C2 C3 C4? No, L=4 here (5 widths). L-1=3 factors in prefix: C1 C2 C3.
#   C1:3x4, C2:4x1, C3:1x4, C4:4x3. prefix C1 C2 C3 (3x4) passes through width-1 (C2) -> rank<=1.
H=(3,4,1,4,3); r=1
C1=sp.Matrix([[1,0,0,0],[0,0,0,0],[0,0,0,0]])  # 3x4
C2=sp.Matrix([[1],[0],[0],[0]])                 # 4x1
C3=sp.Matrix([[1,0,0,0]])                       # 1x4
C4=sp.Matrix([[1,0,0],[0,0,0],[0,0,0],[0,0,0]]) # 4x3
analyze("[F1] (3,4,1,4,3) r=1, bottleneck at middle width-1, wide ends", H, r, [C1,C2,C3,C4])
print()

# (2,3,3) r=2: M=(0,1,1). Bottleneck only at H0=2=r (END). The interior width 3 > r. prefix C1 (2x3),
#   suffix C2 (3x3). rank(C1)<=2, rank(C2) can be 3! suffix rowspace dim could be 3 > r=2.
#   Does rank(J) stay nReg=2*(2+3-2)=6? ambient=2*3+3*3=15.
H=(2,3,3); r=2
C1=sp.Matrix([[1,0,0],[0,1,0]])                  # 2x3 rank2
C2=sp.Matrix([[1,0,0],[0,1,0],[0,0,1]])          # 3x3 rank3 (FULL) -> suffix rowspace dim 3 > r
analyze("[F2] (2,3,3) r=2 END bottleneck H0=2=r; suffix C2 FULL rank 3 > r", H, r, [C1,C2])
print()

# (3,3,2) r=2: M=(1,1,0). Bottleneck only at H_last=2=r (END). prefix C1 (3x3) rank up to 3 > r.
H=(3,3,2); r=2
C1=sp.Matrix([[1,0,0],[0,1,0],[0,0,1]])          # 3x3 FULL rank3 -> prefix colspace dim 3 > r
C2=sp.Matrix([[1,0],[0,1],[0,0]])                # 3x2 rank2
analyze("[F3] (3,3,2) r=2 END bottleneck H_last=2; prefix C1 FULL rank 3 > r", H, r, [C1,C2])
print()

print("="*72)
print("ATTACK G — force prefix/suffix rank DEFICIENT below r at a valid rank-r deepest (the real break)")
print("="*72)
# For rank(J) < nReg we need rank(C_1..C_{L-1}) < r OR rank(C_2..C_L) < r. But product = B rank r forces
#   rank(C_1..C_{L-1}) >= r and rank(C_2..C_L) >= r. So neither can be < r. => surjectivity always holds?!
# This is the crux. Let me try HARD to violate it: a deepest where the LAST factor C_L is rank-deficient
#   so that C_1..C_{L-1} must compensate... but product rank r forces prefix rank >= r anyway.
# (3,1,3) r=1: prefix C1 (3x1) rank<=1, must be exactly 1 (else product 0 != B). suffix C2 rank 1.
#   Try C1 = [0,0,0]^T? then product 0, not B. invalid. C1 must be nonzero -> rank 1. forced.
# Try a chain (4,1,1,4) r=1: prefix C1 C2 (4x1) through width-1. If C2=0 then prefix 0 -> product 0 invalid.
#   forced rank 1. The bottleneck FORCES prefix/suffix rank = r. So rank(J)=nReg structurally.
# CONCLUSION TEST: (4,1,4) with C1 a nonzero 4x1, C2 nonzero 1x4 -> any nonzero gives rank(J)=nReg?
H=(4,1,4); r=1
import itertools
bad=[]
testvecs = [sp.Matrix([1,2,3,4]), sp.Matrix([0,0,1,0]), sp.Matrix([1,1,0,0]), sp.Matrix([5,0,0,7])]
testrows = [sp.Matrix([[1,1,1,1]]), sp.Matrix([[0,0,0,1]]), sp.Matrix([[2,0,3,0]])]
for c1 in testvecs:
    for c2 in testrows:
        rk,nr = analyze(f"[G] (4,1,4) C1={list(c1)} C2={list(c2[0,:])}", H, r, [c1, c2])
        if rk != nr: bad.append((c1,c2,rk))
print(f"\n   any mismatch among forced-rank-1 (4,1,4) bases? {bad if bad else 'NONE'}")
