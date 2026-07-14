from functools import lru_cache
from itertools import product
from fractions import Fraction
import random

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def binding_cuts(M):
    mA=minAdm(M)
    return [t for t in range(min(M[0],M[1])+1)
            if (M[0]-t)*(M[1]-t)+minAdm((t,)+tuple(M[2:]))==mA]
def rho(M): return min(M[1:])
def rev(M): return tuple(reversed(M))

def failing_cut(M):
    """return the (t,u,a,b) of the FIRST pivot-divergent cut (strict conv), or None."""
    r=rho(M)
    for t in binding_cuts(M):
        if t>=1 and t*r < minAdm((t,)+tuple(M[2:])):
            return (t,t,M[0]-t,M[1]-t)
        for j in range(1, min(M[0]-t,M[1]-t)+1):
            u=t+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            if u*r < minAdm((u,)+tuple(M[2:])):
                return (t,u,a,b)
    return None

def pivot_ok(M): return failing_cut(M) is None

# =================================================================
# CRUX 1: does the co-minimizer rho_comin >= a+b-1 RESCUE the pivot block?
# i.e. even with the BEST deep rank the co-minimizer allows, is u*rho still < minAdm?
# =================================================================
print("="*70)
print("CRUX 1: co-minimizer NON-rescue of the pivot block")
badboth=[]
for Ln in [3,4,5,6]:
    for M in product(range(1,7),repeat=Ln):
        if not pivot_ok(M) and not pivot_ok(rev(M)):
            badboth.append(M)
print("both-ends pivot-bad chains (strict):", len(badboth))

# For each, at its failing cut, is the binding cut DEGENERATE (b*=0, co-min N/A),
# or if NONdegenerate does u*rho STILL fail even with the co-minimizer optimistic rho?
deg=0; nondeg_still_fail=0; rescued=0
for M in badboth:
    fc = failing_cut(M)
    t,u,a,b = fc
    astar=M[0]-t; bstar=M[1]-t   # coranks at the BINDING cut t
    r=rho(M)
    Mred_u=(u,)+tuple(M[2:])
    # optimistic deep rank = generic min-width (this IS what pivot sees); co-min gives >= a*+b*-1
    # optimistic = max(min-width, a*+b*-1) capped by tailMin of reduced chain
    comin_lb = max(0, astar+bstar-1)
    tailcap = min(Mred_u) if len(Mred_u)>=2 else Mred_u[0]
    rho_opt = min(max(r, comin_lb), tailcap)   # best deep rank consistent with co-min + generic
    if bstar==0 or astar==0:
        deg+=1
    else:
        # nondegenerate binding cut: does u * rho_opt still under-deliver?
        if u*rho_opt < minAdm(Mred_u):
            nondeg_still_fail+=1
        else:
            rescued+=1
print(f"  failing cut at a DEGENERATE binding cut (a*|b*=0, co-min N/A): {deg}")
print(f"  NONdeg binding cut, pivot STILL fails even w/ optimistic co-min rho: {nondeg_still_fail}")
print(f"  would be RESCUED by co-min rho (route-B might survive here): {rescued}")

# =================================================================
# CRUX 2: independent EXACT verification of the pivot-map rank = u*rho
# for the minimal counterexamples, over the rationals with a generic deep product.
# =================================================================
print("="*70)
print("CRUX 2: exact pivot-map rank check (independent of C_hle chle_mc.py)")
def deep_product_generic(M):
    """generic product of A1(M1xM2) A2(M2xM3)...  = Q of shape M1 x M_last, over Q (rationals)."""
    import numpy as np
    mats=[]
    for i in range(1,len(M)-1):
        mats.append(np.array([[Fraction(random.randint(1,97),1) for _ in range(M[i+1])] for _ in range(M[i])]))
    Q=mats[0]
    for A in mats[1:]:
        Q = Q.dot(A)
    return Q  # M1 x M_last

def frac_matrix_rank(Mtx):
    # exact Gaussian elimination rank over Fraction
    import numpy as np
    Amat=[[Fraction(x) for x in row] for row in Mtx.tolist()]
    rows=len(Amat); cols=len(Amat[0]) if rows else 0
    r=0
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if Amat[i][c]!=0: piv=i; break
        if piv is None: continue
        Amat[r],Amat[piv]=Amat[piv],Amat[r]
        inv=Fraction(1,1)/Amat[r][c]
        Amat[r]=[x*inv for x in Amat[r]]
        for i in range(rows):
            if i!=r and Amat[i][c]!=0:
                f=Amat[i][c]; Amat[i]=[a-f*b for a,b in zip(Amat[i],Amat[r])]
        r+=1
        if r==rows: break
    return r

import numpy as np
for M in [(2,1,2),(3,2,3),(3,2,4),(4,2,4)]:
    # pivot map at the failing cut u:  (P: uxu, B12: uxb) -> P*Q_p + B12*Q_b
    fc=failing_cut(M); t,u,a,b=fc
    # build Q = generic deep product (M1 x M_last); split rows into Q_p (u) and Q_b (b)
    # here M1 = M[1]; deep product Q is M1 x M_last.
    oks=[]
    for _ in range(6):
        Q=deep_product_generic(M)              # M1 x M_last
        Ml=M[-1]; M1=M[1]
        # map domain dim = u*u (P) + u*b (B12); build the linear map matrix, image in u x Ml
        Qp=Q[0:u,:]; Qb=Q[u:u+b,:]
        # basis vectors: P has u*u entries, B12 has u*b entries; assemble columns
        cols=[]
        # P e_{ij}: contributes row i of output = (e_ij P) * Qp -> output row i = Qp row j
        import itertools
        for i in range(u):
            for j in range(u):
                out=np.zeros((u,Ml),dtype=object)
                out[i,:]=Qp[j,:]
                cols.append(out.flatten())
        for i in range(u):
            for j in range(b):
                out=np.zeros((u,Ml),dtype=object)
                out[i,:]=Qb[j,:]
                cols.append(out.flatten())
        Mmap=np.array(cols).T   # (u*Ml) x (u*u+u*b)
        rk=frac_matrix_rank(Mmap)
        oks.append(rk)
    r=rho(M)
    print(f"  M={M} cut u={u}: pivot-map rank = {min(oks)}..{max(oks)}  (predicted u*rho={u*r})  minAdm(red)={minAdm((u,)+tuple(M[2:]))}  => codim {u*r} < {minAdm((u,)+tuple(M[2:]))}: {u*r<minAdm((u,)+tuple(M[2:]))}")
