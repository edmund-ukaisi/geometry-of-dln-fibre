"""
Route-B adjudication: does every nondegenerate >=3-width chain have a front-OR-back
END whose head-split front-peel avoids the divergent off-sector?

Exact integer arithmetic. minAdm matches the Lean layer-peel recursion
(RouteMLayerSplit.minAdmRec) exactly.  redChain t M = (t, M2,...,ML).

Two candidate divergence criteria at chain M, binding cut t*, cut u=t*+j:
  a = M0-u, b = M1-u.
  (PIVOT, C_hle)   rho = min(M1,...,ML);  DIVERGENT iff u*rho < minAdm(redChain u M).
                   Applies at every cut u in [t*, min(M0,M1)] (j>=0), u>=1.  GENUINE route wall.
  (CORANK, tobl3b) floor = M2 if L=0 else min(M1,ML)-j;  DIVERGENT iff floor < a+b.
                   Applies at proper off-sectors (a,b>=1, j>=1).  BOUND ARTIFACT (truly finite).
"""
from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 1: return 0
    if len(M) == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def binding_cuts(M):
    mA = minAdm(M)
    return [t for t in range(min(M[0],M[1])+1)
            if (M[0]-t)*(M[1]-t)+minAdm((t,)+tuple(M[2:]))==mA]

def rho_minwidth(M):
    return min(M[1:])          # generic rank of the deep product Q (M1 x ML)

def pivot_divergent_cuts(M):
    """cuts u where the head-split PIVOT block diverges (genuine route wall)."""
    out=[]
    rho = rho_minwidth(M)
    for t in binding_cuts(M):
        for u in range(t, min(M[0],M[1])+1):     # j = u-t >= 0
            if u < 1: continue
            Mp = (u,) + tuple(M[2:])
            if u*rho < minAdm(Mp):
                out.append((t,u,u-t,M[0]-u,M[1]-u))
    return out

def corank_divergent_shells(M):
    """proper off-sector shells where the CORANK weight fails the honest floor (bound artifact)."""
    out=[]
    L0 = (len(M)==3); ML=M[-1]; M1=M[1]; M2=M[2]
    for t in binding_cuts(M):
        r = min(M[0]-t, M1-t)
        for j in range(1, r+1):
            u=t+j; a=M[0]-u; b=M1-u
            if a<1 or b<1: continue
            floor = M2 if L0 else min(M1,ML)-j
            if floor < a+b:
                out.append((t,u,j,a,b,floor))
    return out

def front_good_pivot(M):
    return len(pivot_divergent_cuts(M))==0
def front_good_corank(M):
    return len(corank_divergent_shells(M))==0
def front_good_both(M):        # S1-mountain-as-built covers the head-split route at M
    return front_good_pivot(M) and front_good_corank(M)

def rev(M): return tuple(reversed(M))

# ---------- (0) Is PIVOT >= CORANK (pivot wall a superset)? ----------
print("="*70)
print("(0) Relationship of the two walls over widths 1..6, lengths 3..6")
piv_only=0; cor_only=0; both_bad=0; n_chains=0; degenerate=0
for Ln in [3,4,5,6]:
    for M in product(range(1,7),repeat=Ln):
        n_chains+=1
        pd = front_good_pivot(M); cd = front_good_corank(M)
        if not pd and cd: piv_only+=1        # pivot fails, corank ok
        if pd and not cd: cor_only+=1        # corank fails, pivot ok
        if not pd and not cd: both_bad+=1
print(f"  chains scanned: {n_chains}")
print(f"  pivot-diverges but corank-ok : {piv_only}")
print(f"  corank-fails but pivot-ok    : {cor_only}   (if 0 => PIVOT wall superset of CORANK)")
print(f"  both bad                     : {both_bad}")

# ---------- (1) THE ROUTE-B CLAIM: every chain has a good END ----------
print("="*70)
print("(1) ROUTE-B per-node claim: front-good(M) OR front-good(rev M)?")
for crit_name, crit in [("PIVOT", front_good_pivot),
                        ("CORANK", front_good_corank),
                        ("BOTH(S1-as-built)", front_good_both)]:
    bad_both_ends=[]
    for Ln in [3,4,5,6]:
        for M in product(range(1,7),repeat=Ln):
            if not crit(M) and not crit(rev(M)):
                bad_both_ends.append(M)
    print(f"  [{crit_name:18s}]  chains bad from BOTH ends: {len(bad_both_ends)}")
    for M in bad_both_ends[:12]:
        print("       BADBOTH", M)
