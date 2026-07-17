"""
Exact-N verification of d1split's two corners for the d=1, a>=u arm.
minAdmRec transcribed from RouteMLayerSplit.lean.
"""
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdmRec(M):
    n=len(M)
    if n<=1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
def redChain(t,M): return (t,)+M[2:]
def gen(ar,w):
    for L in ar:
        for M in product(range(1,w+1),repeat=L): yield M

# Enumerate d=1, a>=u cuts (b=1 focus, but check both a=1 and b=1).
# CORNER (i): radial-peel reaches full 1/2 minAdm(M) iff peel(charge ab) + hIH(redChain u M) closes,
#   i.e. cut-soundness minAdm(M) <= ab + minAdm(redChain u M).  (should be 0 fails)
# CORNER (ii): {Q_b->0} tall reduction -> hIH((M0,M2,...,M_last)) [M1-deleted chain].
#   Need minAdm(M1deleted) >= minAdm(M) for the full threshold.  If FALSE, resolution (a) [bounded-in-Gamma,
#   pivot-only cap] UNDERSHOOTS near {Q_b->0}, so resolution (b) [joint [C|gamma] atlas] is required.
ci_fail=0; ci_total=0
cii_fail=0; cii_total=0; cii_examples=[]
# also: the pivot-only cap minAdm(redChain u M) vs minAdm(M) (the gap the bounded branch caps at)
gap_ex=[]
for M in gen([4,5],6):
    if len(M)<3: continue
    M0,M1=M[0],M[1]; mA=minAdmRec(M)
    for t in range(1,min(M0,M1)+1):
        a=M0-t; b=M1-t; d=min(a,b); u=t
        if d!=1: continue
        if a<u: continue   # a>=u arm
        ab=a*b
        # corner (i): cut-soundness at the peel+red charge
        ci_total+=1
        rc = redChain(u,M)  # (u, M2, ..., M_last)
        if mA > ab + minAdmRec(rc): ci_fail+=1
        # corner (ii): M1-deleted chain (M0, M2, ..., M_last)
        if len(M)>=4:  # need M2 to exist as a real deletion (arity>=4 so M1-deletion is a >=3 chain)
            M1del = (M0,)+M[2:]
            cii_total+=1
            if minAdmRec(M1del) < mA:
                cii_fail+=1
                if len(cii_examples)<6: cii_examples.append((M,t,f"minAdm(M1del {M1del})={minAdmRec(M1del)} < minAdm(M)={mA}"))
print("CORNER (i) cut-soundness minAdm(M) <= ab + minAdm(redChain u M):  fails", ci_fail, "/", ci_total)
print("CORNER (ii) minAdm((M0,M2,...)) >= minAdm(M) [M1-deleted]:  fails", cii_fail, "/", cii_total)
for e in cii_examples: print("   (ii)-fail:", e)
