from functools import lru_cache
import itertools
# ============================================================
# (A) THE DISTILLED SHARING OBSTRUCTION (why a threshold-only invariant fails; why the resolution
#     must carry symbolic divisor SUPPORT). RLCT of a monomial-sum f=∑ x^{α} via the exact toric formula
#        rlct(f) = min_{w>0} (∑_i w_i) / (min_α ⟨w,α⟩)      [verified on x², x²+y² below].
# ============================================================
from scipy.optimize import linprog
def rlct_monsum(monos):
    # minimize (∑w)/(min_α ⟨w,α⟩) over w>0. Scale so min_α⟨w,α⟩ = 1 -> minimize ∑w s.t. ⟨w,α⟩>=1, w>=eps.
    n=len(monos[0])
    # variables w_1..w_n ; minimize sum w ; constraints ⟨w,α⟩ >= 1  (i.e. -⟨w,α⟩ <= -1); w>=0
    c=[1.0]*n
    A_ub=[[-a for a in alpha] for alpha in monos]; b_ub=[-1.0]*len(monos)
    res=linprog(c,A_ub=A_ub,b_ub=b_ub,bounds=[(0,None)]*n,method='highs')
    return res.fun
print("=== (A) exact RLCT via toric formula (sanity: x²=0.5, x²+y²=1.0) ===")
print("  rlct(x²)          =", rlct_monsum([[2]]))
print("  rlct(x²+y²)       =", rlct_monsum([[2,0],[0,2]]))
print("  --- the sharing obstruction (identical 'light data', different value) ---")
print("  rlct(⟨δx,δy⟩)    = δ²x²+δ²y², vars(δ,x,y):", rlct_monsum([[2,2,0],[2,0,2]]), " (SHARED δ -> 1/2)")
print("  rlct(⟨δ1x,δ2y⟩)  = δ1²x²+δ2²y², vars(δ1,δ2,x,y):", rlct_monsum([[2,0,2,0],[0,2,0,2]]), " (SEPARATE δ -> 1)")
print("  => a threshold-only (per-row multiplicity) invariant cannot tell these apart => INSUFFICIENT.")

# ============================================================
# (B) Aoyagi terminal-divisor exponent  M_{s,k} = Mval(branch t) and the accounting
#     rlct_core = ½ min_t Mval(t) = ½ minAdm ; EVERY branch divisor has threshold ≥ ½ minAdm.
# ============================================================
def Mval_branch(M,t):   # t=(t^1,...,t^L), worked-tex terminal exponent formula
    L=len(M)-1; s=(M[0]-t[0])*(M[1]-t[0])
    for j in range(2,L+1): s+=(t[j-2]-t[j-1])*(M[j]-t[j-1])
    return s
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-x)*(M[1]-x)+minAdm((x,)+M[2:]) for x in range(min(M[0],M[1])+1))
def all_branches(M):
    # weakly-decreasing rank profile t^1>=t^2>=...>=t^L>=0, t^1<=min(M0,M1), t^j<=M^{(j+1)}
    L=len(M)-1; out=[]
    def rec(prefix,j,ub):
        if j>L: out.append(tuple(prefix)); return
        hi=min(ub, M[j] if j>=2 else min(M[0],M[1]))  # t^j <= t^{j-1} and admissible bound
        for v in range(hi+1): rec(prefix+[v],j+1,v)
    rec([],1, min(M[0],M[1]))
    return out
print("\n=== (B) every terminal divisor exponent Mval(branch) ≥ minAdm  (so all thresholds ≥ ½minAdm) ===")
for M in [(3,3,3,3),(3,3,4),(2,2,2,2),(3,3,3,3,3)]:
    br=all_branches(M); vals=sorted(set(Mval_branch(M,t) for t in br)); mm=minAdm(M)
    binding=[t for t in br if Mval_branch(M,t)==mm]
    print(f"  M={M}: minAdm={mm}, ½minAdm={mm/2}; distinct Mval over branches (min..)= {vals[:6]}...; "
          f"min matches minAdm: {vals[0]==mm}; binding branches={binding[:4]}")

# ============================================================
# (C) LAYER-BY-LAYER charge accumulation onto the binding divisor (the recursion the resolution runs).
#     At the binding branch, peeling layer j adds charge a_j; the charges ADD onto ONE divisor to Mval.
#     The Hölder route saturates ½minAdm(redChain) at layer 1 and drops the coupling; the resolution
#     keeps accumulating on the same divisor.
# ============================================================
def binding_branch(M):
    L=len(M)-1; best=None; bt=None
    for t in all_branches(M):
        v=Mval_branch(M,t)
        if best is None or v<best: best=v; bt=t
    return bt,best
print("\n=== (C) per-layer charge accumulation on the binding divisor (should sum to Mval=minAdm) ===")
for M in [(3,3,3,3),(3,3,3,3,3),(4,4,4,4)]:
    t,val=binding_branch(M); L=len(M)-1
    charges=[(M[0]-t[0])*(M[1]-t[0])]
    for j in range(2,L+1): charges.append((t[j-2]-t[j-1])*(M[j]-t[j-1]))
    # cumulative "budget spent" vs ½minAdm(redChain at that level) [the Hölder saturation]
    print(f"  M={M}: binding t={t}, per-layer charges={charges}, sum={sum(charges)}=minAdm={minAdm(M)} "
          f"[{'OK' if sum(charges)==minAdm(M) else 'X'}]")
