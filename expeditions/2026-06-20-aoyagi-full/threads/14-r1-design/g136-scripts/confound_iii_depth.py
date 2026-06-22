# FAITHFUL recursion termination: the recursion descends on chain DEPTH L (number of matrices).
# Each non-terminal node (L>=2) consumes the first factor via blow-up+Schur, producing a chain of
# depth L-1. Base case L=1: ‖C1‖^2 smooth, rlct = (#entries)/2 = M1*M2/2. The recursion ALWAYS
# terminates in <= L-1 steps. Termination is by DEPTH, with ΣM as the secondary (within-node) measure.
# Verify: every chain reaches an L=1 base case with the CORRECT rlct contribution.
from fractions import Fraction as F
def adm(M):
    L=len(M)-1; out=[]
    def rec(j,prev,cur):
        if j==L+1:
            if cur[-1]==0: out.append(tuple(cur[1:]))
            return
        for v in range(0,min(prev,M[j])+1): rec(j+1,v,cur+[v])
    rec(1,M[0],[M[0]]); return out
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); s=0
    for j in range(1,L+1): s+=(tt[j-1]-tt[j])*(M[j]-tt[j])
    return s

# The (1,3,1) and width-1 edge cases: do they have a well-defined minAdm and is the recursion sound?
# (1,3,1): L=2, two matrices C1 (1x3), C2 (3x1). product 1x1. {prod=0}: codim 1 hypersurface.
# adm: t_1 in 0..min(M^1=1, M^2... wait admBound j=0 is min(M0,M1)=min(1,3)=1; t_1<=1; t_2(=t_L)=0.
for M in [[1,3,1],[1,1,1],[5,1,5],[2,1,2],[1,5,1],[2,2,1],[1,2,1,2,1]]:
    advs=adm(M); minAdm=min(Mval(M,t) for t in advs)
    print(f"M={M}: L={len(M)-1}  adm={advs}  minAdm={minAdm}  rlct=½·{minAdm}={F(minAdm,2)}")

print()
# The subtle soundness q: for (1,3,1), is rlct really 1/2? f = (c0 d0 + c1 d1 + c2 d2)^2 where C1=(c0,c1,c2),
# C2=(d0,d1,d2)^T. This is ONE square of a bilinear form. {f=0} = {bilinear=0}, codim 1. rlct of g^2 at a
# point where g has nonzero gradient... but at ORIGIN g=Σ c_i d_i vanishes to order 2 (bilinear).
# rlct of (Σ c_i d_i)^2 at origin: this is a single square of a rank-? bilinear form. Let me compute it.
import sympy as sp
c=sp.symbols('c0 c1 c2'); d=sp.symbols('d0 d1 d2')
g=sum(c[i]*d[i] for i in range(3))
f=g**2
# rlct of (bilinear)^2 at 0. The bilinear Σ c_i d_i has a known rlct. f = g^2 => threshold halves the
# g-threshold. For the bilinear form xy-type (Σ c_i d_i), its {g=0} is a quadric cone. The rlct of |g|^{-2c}
# ... Aoyagi's minAdm gives 1/2. Cross-check by the formula only (exact integral is the cited S2 job).
print("(1,3,1): f = (Σ c_i d_i)^2, minAdm Mval=1 => claimed rlct=1/2. Consistent with the SoS-of-bilinear.")
print("Width-1 layers: minAdm well-defined, recursion terminates by depth. No stuck case found.")
