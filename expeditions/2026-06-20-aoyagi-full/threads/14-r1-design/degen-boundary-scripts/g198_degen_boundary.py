import sympy as sp
# DEGENERATE BOUNDARY (#70): some M_s = 0 (i.e. r = H_s at layer s). The reduced widths M = H − r.
# M_s=0 ⟹ the reduced core dlnLoss M 0 vanishes (lambdaCore=0); compute rlctAt(deepest) DIRECTLY.
# CLAIM: rlctAt(deepest) = nReg/2 = r(H_0+H_L−r)/2 = aoyagiLambda. The loss at the degenerate deepest pt
# is a rank-nReg Morse-Bott quadratic + flat complement (vanished-core + gauge) ⟹ rlctAt = nReg/2.
#
# Verify: (i) Hessian rank = nReg at the deepest; (ii) flat complement; (iii) rlct = nReg/2.
# The deepest point: a rank-r-exact factorization of B (here B=0 core, deepest = the all-rank-r config).
# Actually for the boundary r=H_s, the chain bottlenecks: rank ≤ H_s = r everywhere, so a rank-r product
# is "automatic" through the width-H_s layer. dlnLoss H B with B=0 core: deepest = origin? Let me use the
# audit cases.

def nReg(H, r):  # = r(H_0 + H_last - r)
    return r*(H[0] + H[-1] - r)

# CASE (3,1,3), r=1: H=(3,1,3), middle width 1 = r ⟹ M=(3-1,1-1,3-1)=(2,0,2), M_1=0 degenerate.
# Chain C1:3x1, C2:1x3 (the H widths). The product C1 C2 is 3x3 rank ≤ 1 ALWAYS (through width-1).
# Core dlnLoss: ‖C1 C2 - B‖², B rank 1. deepest = rank-exact (both rank 1). 
# Let me set up the FULL loss at the deepest and compute the Hessian rank.
print("="*64)
print("CASE (3,1,3) r=1: H=(3,1,3), M=(2,0,2) [M_1=0 degenerate], nReg = 1*(3+3-1) = ", nReg((3,1,3),1))
print("="*64)
# B = rank-1 target, e.g. B = e0 e0^T (3x3). Deepest: C1=[1,0,0]^T (3x1), C2=[1,0,0] (1x3), C1 C2 = e0 e0^T = B.
# Local: C1 = (1+u0, u1, u2)^T, C2 = (1+v0, v1, v2). product = C1 C2 (3x3), loss = ‖C1 C2 - B‖².
u = sp.symbols('u0:3', real=True); v = sp.symbols('v0:3', real=True)
C1 = sp.Matrix([[1+u[0]],[u[1]],[u[2]]])  # 3x1
C2 = sp.Matrix([[1+v[0], v[1], v[2]]])     # 1x3
P = sp.expand(C1*C2)  # 3x3
B = sp.zeros(3,3); B[0,0]=1
F = sp.expand(sum((P-B)[i,j]**2 for i in range(3) for j in range(3)))
allv = list(u)+list(v)
# Hessian at deepest (all u,v = 0):
H_mat = sp.hessian(F, allv).subs({x:0 for x in allv})
rk = H_mat.rank()
print(f"  loss F = ‖C1 C2 - B‖², 6 local vars (u0..u2, v0..v2). Hessian rank at deepest = {rk}")
print(f"  nReg = {nReg((3,1,3),1)}. Match: {rk == nReg((3,1,3),1)}")
# rlct of a rank-k nondeg quadratic + flat = k/2:
print(f"  ⟹ rlctAt(deepest) = nReg/2 = {sp.Rational(nReg((3,1,3),1),2)} (audit: 5/2 ✓)" if rk==nReg((3,1,3),1) else "  MISMATCH")
# flat complement: 6 - rk directions are flat (the gauge GL_1 + the vanished-core)
print(f"  flat complement: {len(allv)} - {rk} = {len(allv)-rk} flat directions (gauge GL_r + vanished core M_1=0)")
print()

print("="*64)
print("CASE (1,1) r=1: H=(1,1), M=(0,0) [both degenerate], nReg = 1*(1+1-1) = ", nReg((1,1),1))
print("="*64)
# H=(1,1), L=1, single layer C1: 1x1 scalar. B=rank1=scalar≠0, say B=1. loss=(C1 - 1)². deepest C1=1.
c = sp.symbols('c', real=True); F2 = (c-1)**2  # wait that's L=1 single matrix, no product. 
# Actually (1,1) r=1: H_0=1,H_1=1, one matrix C:1x1. mult = C. B=1. loss=(C-B)²=(C-1)². deepest C=1.
F2 = sp.expand((c - 1)**2)
H2 = sp.hessian(F2, [c]).subs({c:0})  # hessian is constant 2
rk2 = H2.rank()
print(f"  loss (C-1)², 1 var. Hessian rank at deepest = {rk2}, nReg = {nReg((1,1),1)}. Match: {rk2==nReg((1,1),1)}")
print(f"  ⟹ rlctAt = nReg/2 = {sp.Rational(nReg((1,1),1),2)} (audit: 1/2 ✓)")
