from scipy.optimize import linprog
from functools import lru_cache
def rlct_monsum(monos):
    n=len(monos[0]); 
    return linprog([1.0]*n,A_ub=[[-a for a in al] for al in monos],b_ub=[-1.0]*len(monos),bounds=[(0,None)]*n,method='highs').fun

print("=== (1) SHARED vs SEPARATE at TWO coupled blocks (does the sharing change the value at 2 blocks?) ===")
# terminal-monomial models. SHARED: b1=u, b2=u·v (layer-1 radial u SHARED into b2). loss ~ b1²x²+b2²y².
# SEPARATE (naive fresh-per-block): b1=u1, b2=u2·v (no shared u). loss ~ b1²x²+b2²y².
shared   = rlct_monsum([[2,0,0,0],[2,2,0,0]])       # u²x², u²v²y²   vars (u,v,x,y)
separate = rlct_monsum([[2,0,0,0,0],[0,2,2,0,0]])   # u1²x², u2²v²y² vars (u1,u2,v,x,y)
print(f"  SHARED   (u shared: u²x², u²v²y²)      rlct = {shared}")
print(f"  SEPARATE (fresh: u1²x², u2²v²y²)       rlct = {separate}")
print(f"  => sharing {'CHANGES' if abs(shared-separate)>1e-9 else 'does NOT change'} the value at 2 blocks"
      f" => shared-support tracking is {'NECESSARY' if abs(shared-separate)>1e-9 else 'not needed'} beyond 1 block")

# also the 1-block minimal (control): ⟨δx,δy⟩ shared=½ vs ⟨δ1x,δ2y⟩ separate=1
print(f"  [control 1-block] ⟨δx,δy⟩={rlct_monsum([[2,2,0],[2,0,2]])}  vs ⟨δ1x,δ2y⟩={rlct_monsum([[2,0,2,0],[0,2,0,2]])}")

print("\n=== (2) iterated single-radial charge accounting reaches minAdm on MULTI-corank chains ===")
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def Mval(M,T):
    L=len(T);s=0
    for j in range(L):
        tp=M[0] if j==0 else T[j-1]; s+=(tp-T[j])*(M[j+1]-T[j])
    return s
import itertools
def adm(M,T):
    L=len(T)
    for j in range(L):
        if T[j]>admBound(M,j) or (j>0 and T[j]>T[j-1]): return False
    return T[L-1]==0
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0:return 0
    if L==1:return M[0]*M[1]
    return min((M[0]-x)*(M[1]-x)+minAdm((x,)+M[2:]) for x in range(min(M[0],M[1])+1))
for M in [(3,3,3,4),(4,4,4,4),(3,3,3,3,3),(4,4,4,4,4)]:
    cone=[T for T in itertools.product(*[range(admBound(M,j)+1) for j in range(len(M)-1)]) if adm(M,T)]
    mm=minAdm(M); binding=[T for T in cone if Mval(M,T)==mm]
    # per-layer charges on a binding branch (=iterated single-radial charges) sum to Mval=minAdm
    T=binding[0]; ch=[]
    for j in range(len(T)):
        tp=M[0] if j==0 else T[j-1]; ch.append((tp-T[j])*(M[j+1]-T[j]))
    # corank of layer-1 drop (block dims)
    print(f"  M={M}: binding T={T}, iterated charges={ch}, Σ={sum(ch)}=minAdm={mm}=½·{2*mm/2}; "
          f"layer-1 corank block ({M[0]-T[0]}×{M[1]-T[0]})")
print("  => the ITERATED single-radial charge accounting (=minAdmRec, banked) reaches minAdm on multi-corank.")
print("     (L=2 single-block ‖XY‖² is banked: routeMBoxThresholdFinite_rrp/_mnp.)")
