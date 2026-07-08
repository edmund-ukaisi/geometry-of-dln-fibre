from functools import lru_cache
from itertools import product

# minAdm via the layer-peeling recursion (matches minAdmRec):
# L=0 (1 width): 0 ; L=1 (2 widths): M0*M1 ; else min_{t<=min(M0,M1)} (M0-t)(M1-t)+minAdm(redChain)
def minadm(M):
    M = tuple(M)
    n = len(M)
    if n == 1: return 0
    if n == 2: return M[0]*M[1]
    best = None
    for t in range(0, min(M[0],M[1])+1):
        red = (t,) + M[2:]
        v = (M[0]-t)*(M[1]-t) + minadm(red)
        best = v if best is None else min(best, v)
    return best

def redchain(t, M): return (t,) + tuple(M[2:])

# Brute-force minAdm = min over admissible strata of Mval, cross-check.
def brute(M):
    M = tuple(M); n=len(M)
    # exponents T over Fin (n-1) (one per matrix boundary? actually Fin L = n-1),
    # admissible: weakly decreasing, T_j <= admBound, T_last = 0.
    L = n-1
    if L==0: return 0
    # admBound: index 0 -> min(M0,M1); index j -> M_{j+1}
    def admbound(j):
        if j==0: return min(M[0],M[1])
        return M[j+1]
    bnds=[admbound(j) for j in range(L)]
    best=None
    ranges=[range(b+1) for b in bnds]
    for T in product(*ranges):
        # weakly decreasing
        if any(T[j+1] > T[j] for j in range(L-1)): continue
        if T[-1] != 0: continue
        # Mval = sum_j (tPrev - T_j)(M_{j+1} - T_j), tPrev(0)=M0, tPrev(j)=T_{j-1}
        val=0
        for j in range(L):
            tprev = M[0] if j==0 else T[j-1]
            val += (tprev - T[j])*(M[j+1]-T[j])
        best = val if best is None else min(best,val)
    return best

for M in [(2,2,2),(3,3,4),(4,4,2,2),(3,3,2,2),(2,2,2,2),(3,3,3,4),(1,2,2),(1,2),(0,2)]:
    a=minadm(M); 
    try: b=brute(M)
    except Exception as e: b=f"err {e}"
    print(f"M={M}: minAdmRec={a}  brute={b}  match={a==b}")

print("\n--- (2,2,2,2) binding paths (front-peel) ---")
M=(2,2,2,2)
for t in range(0,min(M[0],M[1])+1):
    red=redchain(t,M); ch=(M[0]-t)*(M[1]-t); print(f" front t={t}: charge={ch} red={red} minAdm(red)={minadm(red)} sum={ch+minadm(red)} (minAdm(M)={minadm(M)}) binding={ch+minadm(red)==minadm(M)}")
print(" path t=1 then s in (1,2,2):")
M2=(1,2,2)
for s in range(0,min(M2[0],M2[1])+1):
    red=redchain(s,M2); ch=(M2[0]-s)*(M2[1]-s); print(f"   s={s}: charge={ch} red={red} minAdm(red)={minadm(red)} sum={ch+minadm(red)} binding={ch+minadm(red)==minadm(M2)}")

print("\n--- (3,3,4) binding (corank-2 radial) ---")
M=(3,3,4)
for t in range(0,min(M[0],M[1])+1):
    red=redchain(t,M); ch=(M[0]-t)*(M[1]-t); print(f" t={t}: charge={ch}(block {M[0]-t}x{M[1]-t}) red={red} minAdm={minadm(red)} sum={ch+minadm(red)} binding={ch+minadm(red)==minadm(M)}")
