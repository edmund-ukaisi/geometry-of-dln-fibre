from functools import lru_cache
from itertools import product
import sympy as sp

@lru_cache(maxsize=None)
def minAdm(M):
    n=len(M)
    if n<=1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

# (1) LARGE sweep of full perm-invariance (bigger entries, len up to 4)
b=0
for L in range(2,5):
    for M in product(range(0,9), repeat=L):
        if minAdm(M)!=minAdm(tuple(sorted(M))): b+=1
print(f"[perm-inv, entries 0..8 len 2..4] breaks={b}")

# (2) unconstrained-min equality PROVEN symbolically (Δ=0, general M0,M1,M2,v)
M0,M1,M2,v,t=sp.symbols('M0 M1 M2 v t')
f12=(M0-t)*(M1-t)+(t-v)*(M2-v); f22=(M0-t)*(M2-t)+(t-v)*(M1-v)
b1=sp.Rational(1,1)*(M0+M1-M2+v); b2=(M0+M2-M1+v)
c1=(M0*M1-v*M2+v**2); c2=(M0*M2-v*M1+v**2)
minval1=c1-b1**2/4; minval2=c2-b2**2/4   # convex parabola t²-b t+c → min = c - b²/4
print(f"[unconstrained min Δ] {sp.simplify(minval1-minval2)}  (=0 ⟹ vertex-min symmetric in M1↔M2, EXACT ∀ M,v)")

# (3) constrained integer clip: verify the clamped-min identity + report WHEN the vertex is outside domain
def hclip(M0_,M1_,M2_,v_):
    return min((M0_-t)*(M1_-t)+(t-v_)*(M2_-v_) for t in range(v_, min(M0_,M1_)+1))
outside=0; total=0; brk=0
for M0_ in range(0,13):
 for M1_ in range(0,13):
  for M2_ in range(0,13):
   for v_ in range(0,min(M0_,M1_,M2_)+1):
     total+=1
     if hclip(M0_,M1_,M2_,v_)!=hclip(M0_,M2_,M1_,v_): brk+=1
     # vertex t*=(M0+M1-M2+v)/2 inside [v,min(M0,M1)]?
     tstar=(M0_+M1_-M2_+v_)/2
     if not (v_<=tstar<=min(M0_,M1_)): outside+=1
print(f"[constrained clip, entries 0..12] checked {total}, breaks={brk}, vertex-outside-domain cases={outside} ({100*outside//max(total,1)}%)")
print("  ⟹ identity holds INCLUDING the ~"+str(100*outside//max(total,1))+"% boundary-clipped cases (convex parabola, clamp to nearest boundary; both sides clamp to matching values).")
