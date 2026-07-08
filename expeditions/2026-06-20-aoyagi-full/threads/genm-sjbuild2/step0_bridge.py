import itertools
from functools import lru_cache
from fractions import Fraction as F

# ---- combinatorial spine (mirrors RouteMLayerSplit.lean exactly) ----
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def is_adm(M,T):
    L=len(T)
    for j in range(L):
        if T[j]>admBound(M,j): return False
    for i in range(L):
        for j in range(L):
            if i<=j and T[j]>T[i]: return False
    return L<1 or T[L-1]==0
def adm_cone(M):
    L=len(M)-1
    return [T for T in itertools.product(*[range(admBound(M,j)+1) for j in range(L)]) if is_adm(M,T)]
def Mval(M,T):
    s=0
    for j in range(len(T)):
        tprev=M[0] if j==0 else T[j-1]; s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
def redChain(t,M): return (t,)+M[2:]
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-x)*(M[1]-x)+minAdm(redChain(x,M)) for x in range(min(M[0],M[1])+1))

# ---- trace one binding branch's peel: charges, radials (k=1,jac=pq-1), terminal ----
def trace(M,T):
    cur=M; steps=[]
    j=0
    while len(cur)>=3:
        t=T[j]; p=cur[0]-t; q=cur[1]-t; pq=p*q
        steps.append(dict(layer=j+1,cur=cur,t=t,p=p,q=q,pq=pq))
        cur=redChain(t,cur); j+=1
    # cur is now a leaf: Fin 2 (free matrix) or Fin 1 (trivial)
    return steps, cur

def monThreshold_diag(radials):
    # radials: list of (k,jac); returns min_j (jac+1)/(2k), skipping k=0 (⊤)
    vals=[F(jac+1,2*k) for (k,jac) in radials if k>0]
    return min(vals) if vals else None  # None = ⊤

print("="*90)
print("STEP-0 TERMINAL COUNT<->MONOMIAL BRIDGE  (native clear-first R-blowup ledger)")
print(" model: each peel -> fully-shared radial u_j, k_j=1, jac_j=pq_j-1 (radial blowup Jacobian)")
print(" bridge test:  1/2 * minAdm(remChain_terminal)  <=  monomialThreshold(accumulated ledger)")
print("="*90)

anchors = {
  "(3,3,4)":      ((3,3,4),      None),   # None => all binding branches
  "(2,2,2,2)":    ((2,2,2,2),    (1,0,0)),# the named t=1 branch
  "(3,3,3,4)":    ((3,3,3,4),    (1,0,0)),
}

for name,(M,pinT) in anchors.items():
    mm=minAdm(M)
    binding=[T for T in adm_cone(M) if Mval(M,T)==mm]
    print(f"\n### {name}: minAdm={mm}, 1/2*minAdm={F(mm,2)}; binding branches={binding}")
    branches = [pinT] if pinT is not None else binding
    for T in branches:
        tag = "PINNED" if pinT is not None else "binding"
        if T not in binding:
            print(f"   [warn] T={T} not binding (Mval={Mval(M,T)} != {mm})")
        steps,leaf = trace(M,T)
        radials=[(1, s['pq']-1) for s in steps if s['pq']>0]  # pq=0 peels: no radial
        charges=[s['pq'] for s in steps]
        # terminal classification
        if len(leaf)==2:
            term_kind=f"FREE-MATRIX leaf {leaf} (regime-B Morse, charge {leaf[0]*leaf[1]})"
            rem_minAdm = minAdm(leaf)  # = leaf0*leaf1
        else:
            term_kind=f"TRIVIAL leaf {leaf} (arity 0)"
            rem_minAdm = minAdm(leaf) if len(leaf)>=1 else 0
        sum_all = sum(charges)+ (leaf[0]*leaf[1] if len(leaf)==2 else 0)
        mth = monThreshold_diag(radials)
        # the bridge LHS at the monomial terminal uses minAdm(remChain terminal)
        lhs = F(rem_minAdm,2)
        print(f"   T={T} [{tag}]: charges={charges} radials(k,jac)={radials}")
        print(f"      terminal: {term_kind}; minAdm(remChain_term)={rem_minAdm}")
        print(f"      additive soundness: sum(charges)+terminal = {sum_all}  == minAdm {mm}?  {sum_all==mm}")
        print(f"      accumulated diag monomialThreshold = {mth} (= 1/2*min(charges)); NOTE < 1/2*minAdm if multi-peel")
        print(f"      BRIDGE  1/2*minAdm(remChain_term)={lhs}  <=  monThreshold={mth}?  ", 
              ("TRIVIAL(rem=0)" if rem_minAdm==0 else ("N/A: free-matrix -> regime B, not monomial term")))
