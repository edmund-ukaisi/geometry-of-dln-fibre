"""
Vertical-slice exact verification: (3,3,3,4) corank-2 composed (S,J) blow-up recursion.
All checks symbolic (sympy) — exact algebra, not float.

Layers: A0 : 3x3, A1 : 3x3, A2 : 3x4.  F = frobSq(A0 A1 A2).  Target: minAdm = 7, threshold 7/2.
"""
import sympy as sp
from sympy import Rational as R

# ---------------------------------------------------------------------------
# 0. minAdm recursion + binding branch charges  (exact integer arithmetic)
# ---------------------------------------------------------------------------
from functools import lru_cache
@lru_cache(None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 2:
        return M[0]*M[1]
    best = None
    for t in range(min(M[0], M[1]) + 1):
        red = (t,) + M[2:]
        val = (M[0]-t)*(M[1]-t) + minAdm(red)
        best = val if best is None else min(best, val)
    return best

def branch_charges(M, T):
    """charges per boundary for pivot profile T (len L)."""
    ch = []
    cur = list(M)
    for j, t in enumerate(T):
        ch.append((cur[0]-t)*(cur[1]-t))
        cur = [t] + cur[2:]
    return ch

M = (3,3,3,4)
print("minAdm(3,3,3,4) =", minAdm(M), " (target: 7)")
for t1 in range(4):
    print(f"  boundary-0 cut t1={t1}: block=({3-t1})*({3-t1})={ (3-t1)**2}, minAdm(redChain)= {minAdm((t1,3,4))}, sum={(3-t1)**2+minAdm((t1,3,4))}")
print("binding branch T=(1,0,0) charges:", branch_charges(M,(1,0,0)), "sum=", sum(branch_charges(M,(1,0,0))))
print("branch T=(2,1,0) charges:", branch_charges(M,(2,1,0)), "sum=", sum(branch_charges(M,(2,1,0))))
print()

# ---------------------------------------------------------------------------
# 1. Schur block split identity (frobSq_schur_block_split), t=1 pivot at (1,1)
#    frobSq(A0 Q) = frobSq(a * Qtp) + frobSq(C*Qtp + Gamma*Qb)
#    Qtp = Qp + a^{-1} B Qb,  Gamma = D - C a^{-1} B
# ---------------------------------------------------------------------------
def mat(name, r, c):
    return sp.Matrix(r, c, lambda i,j: sp.Symbol(f"{name}_{i}{j}"))

a  = sp.Symbol("a")                 # 1x1 pivot (nonzero on chart)
B  = mat("B",1,2)                   # 1x2
C  = mat("C",2,1)                   # 2x1
D  = mat("D",2,2)                   # 2x2
A0 = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[a]]), B],[C, D]]))   # 3x3
Q  = mat("Q",3,4)                   # 3x4 (stands for A1 A2)
Qp = Q[0:1,:]                       # 1x4
Qb = Q[1:3,:]                       # 2x4

frob = lambda X: sum(v**2 for v in X)
LHS  = frob(A0*Q)
Qtp   = Qp + a**(-1)*B*Qb
Gamma = D - C*a**(-1)*B
RHS   = frob(a*Qtp) + frob(C*Qtp + Gamma*Qb)
print("Schur block split  frobSq(A0 Q) == frobSq(a Qtp)+frobSq(C Qtp+Gamma Qb):",
      sp.simplify(LHS-RHS) == 0)

# ---------------------------------------------------------------------------
# 2. Depth reduction: after shear absorbing a^{-1}B into A1, F = frobSq(H A2)
#    with  H = [[a*v],[C*v + Gamma*W]],  v=row1(A1) 1x3, W=rows23(A1) 2x3.
#    (This is the reduction to a fresh (3,3,4)-shaped core with CONSTRAINED H.)
#    Verify:  frobSq(a*(v A2)) + frobSq((C v + Gamma W) A2) == frobSq(H A2).
# ---------------------------------------------------------------------------
v  = mat("v",1,3)
W  = mat("W",2,3)
A2 = mat("A2",3,4)
H  = sp.Matrix(sp.BlockMatrix([[a*v],[C*v + Gamma*W]]))    # 3x3
lhs2 = frob(a*(v*A2)) + frob((C*v + Gamma*W)*A2)
print("Depth reduction    frobSq(H A2) == a^2||vA2||^2 + ||(Cv+GammaW)A2||^2:",
      sp.simplify(frob(H*A2) - lhs2) == 0)

# Also verify H really is the Schur-split loss re-expressed:  with Q=A1 A2 and
# A1 having row1=v, rows23=W, and applying the unipotent U=[[1,a^{-1}B],[0,I]]
# to A1 (absorbing the Qtp shear), we should reproduce F.
A1full = sp.Matrix(sp.BlockMatrix([[v],[W]]))              # 3x3, row1=v rows23=W
U = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[1]]), a**(-1)*B],[sp.zeros(2,1), sp.eye(2)]]))
A1shear = U*A1full
Qsheared = A1shear*A2
# with A1 sheared, Qtp := row1(Qsheared), Qb := rows23(Qsheared)
Qtp2 = Qsheared[0:1,:]; Qb2 = Qsheared[1:3,:]
Frecon = frob(a*Qtp2) + frob(C*Qtp2 + Gamma*Qb2)
print("Shear-absorb check frobSq(H A2) == reconstructed F after A1-shear:",
      sp.simplify(frob(H*A2) - Frecon) == 0)
print("  (Jacobian of A1 |-> U A1 is det(U)^3 =", sp.det(U)**3, ") -- MP, no det-inverse in Jacobian")
print()

# ---------------------------------------------------------------------------
# 3. corank-2 -> corank-1 crux (chart-lemma-probe): for the 2x2 corank block
#    Delta coupled to downstream Z: ||Delta Z||^2 = u^2 ||Delta' Z||^2 (radial),
#    then unit-triangular clear Delta' -> diag(1, delta'),  delta' = d - a b.
# ---------------------------------------------------------------------------
u = sp.Symbol("u")
Delta = mat("Dl",2,2)             # free 2x2
Z = mat("Z",2,4)                  # downstream 2x4 (rows of A2-product)
# single radial: Delta = u*Delta'
Dp = mat("Dp",2,2)
print("radial factor      ||(u Dp) Z||^2 == u^2 ||Dp Z||^2:",
      sp.simplify(frob(u*Dp*Z) - u**2*frob(Dp*Z)) == 0)
# unit-triangular clear of Dp -> diag(1, delta'), pivot Dp[0,0]!=0
p00 = Dp[0,0]
Lrow = sp.Matrix([[1,0],[-Dp[1,0]/p00,1]])   # clears (1,0)
Rcol = sp.Matrix([[1,-Dp[0,1]/p00],[0,1]])   # clears (0,1)
cleared = Lrow*Dp*Rcol
print("unit clear det(L),det(R):", sp.simplify(sp.det(Lrow)), sp.simplify(sp.det(Rcol)),
      " -> cleared[0,1],[1,0]=", sp.simplify(cleared[0,1]), sp.simplify(cleared[1,0]))
print("  cleared diag = [", sp.simplify(cleared[0,0]),",", sp.simplify(cleared[1,1]),
      "]  (delta' = d - bc/a =", sp.simplify(Dp[1,1]-Dp[1,0]*Dp[0,1]/p00),")")
# residual loss after clearing: ||[[1,0],[0,delta']] (L Z)||^2 = ||row1(LZ)||^2 + delta'^2||row2(LZ)||^2
dprime = sp.simplify(cleared[1,1])
LZ = Lrow*Z
resid = frob(cleared * (Rcol.inv()) * Z)   # loss = ||cleared_diag * (Rcol^{-1} Z)||... check morse split
# Simpler: after L (rows) and R (cols) with cols acting on the Delta side (absorbed into Z' = R^{-1}... ) —
# demonstrate the MORSE split structure on the diagonalised block:
diagblk = sp.diag(1, dprime)
Zc = mat("Zc",2,4)
morse = frob(diagblk*Zc)
print("morse split        ||diag(1,delta') Zc||^2 == ||row1 Zc||^2 + delta'^2||row2 Zc||^2:",
      sp.simplify(morse - (frob(Zc[0:1,:]) + dprime**2*frob(Zc[1:2,:]))) == 0)
