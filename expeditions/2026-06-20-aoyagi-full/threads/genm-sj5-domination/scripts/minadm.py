from functools import lru_cache
from itertools import product

# minAdm via the peel recursion (Lehalleur-Rimanyi / cert transversality-recursion §1):
#   base arity-2 (n,m): minAdm = n*m
#   minAdm(M) = min_{0<=t<=min(M0,M1)} [ (M0-t)(M1-t) + minAdm( (t,M2,...,) ) ]
# redChain(t,M) = (t, M2, M3, ...)  (drop M0,M1, insert t).  peelCharge=(M0-t)(M1-t).

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    assert len(M) >= 2
    if len(M) == 2:
        return M[0]*M[1]
    best = None; arg = None
    for t in range(0, min(M[0], M[1])+1):
        red = (t,) + M[2:]
        val = (M[0]-t)*(M[1]-t) + minAdm(red)
        if best is None or val < best:
            best = val; arg = t
    return best

@lru_cache(maxsize=None)
def bindingCut(M):
    # least t achieving the min (the 'binding cut' t★), among NONTRIVIAL if possible
    M = tuple(M)
    best = None; args = []
    for t in range(0, min(M[0], M[1])+1):
        red = (t,) + M[2:]
        val = (M[0]-t)*(M[1]-t) + minAdm(red)
        if best is None or val < best:
            best = val; args = [t]
        elif val == best:
            args.append(t)
    return best, args

def analyze(M):
    M = tuple(M)
    best, args = bindingCut(M)
    out = []
    for t in args:
        a = M[0]-t; b = M[1]-t
        M2 = M[2] if len(M) >= 3 else None      # width of A_cor columns / deeper Gram size
        pW_b1 = max(0, a-(M2-1)) if (b==1 and M2 is not None) else None
        red = (t,)+M[2:]
        out.append(dict(t=t,a=a,b=b,M2=M2,peel=a*b,minAdm_red=minAdm(red),
                        pW_b1=pW_b1, a_lt_M2=(a<M2) if M2 else None))
    return best, out

# Sweep chains: arity 3 and 4 (lengths 4 and 5), widths 1..5
print("=== arity-3 chains M=(m0,m1,m2,m3) : binding cut(s), a,b,M2, p_W(b=1), a<M2? ===")
bad=[]
for M in product(range(1,6),repeat=4):
    if min(M)==0: continue
    best, cuts = analyze(M)
    for c in cuts:
        if c['b']>=1 and c['a']>=1 and c['M2'] is not None:
            if c['b']==1:
                if not c['a_lt_M2']:
                    bad.append((M,c))
print("total arity-3 nondegenerate-cut chains with b==1 and a>=M2 (p_W>0):", len(bad))
for M,c in bad[:40]:
    print("  M=",M,"cut",{k:c[k] for k in ('t','a','b','M2','peel','minAdm_red','pW_b1')})

print()
print("=== spot anchors ===")
for M in [(3,3,2,2),(3,3,4),(4,4,4,4),(2,5,5,5),(3,3,3,4),(5,5,2,2),(4,4,2,2),(5,5,2,3),(5,4,2,2),(4,2,2,2)]:
    best,cuts=analyze(M)
    print(f"M={M} minAdm={best} carrierThr={best/2}")
    for c in cuts:
        print("   ",{k:c[k] for k in ('t','a','b','M2','peel','minAdm_red','pW_b1','a_lt_M2')})
