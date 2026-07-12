from functools import lru_cache
from itertools import product, permutations

@lru_cache(maxsize=None)
def minAdm(M):
    # M a tuple (M0,...,M_L). L+1 = len(M). recursion peels the front pair.
    n = len(M)
    if n <= 1: return 0
    if n == 2: return M[0]*M[1]
    M0,M1 = M[0],M[1]
    best = None
    for t in range(min(M0,M1)+1):
        val = (M0-t)*(M1-t) + minAdm((t,)+M[2:])
        best = val if best is None else min(best,val)
    return best

# ---- PROVE-OR-REFUTE: minAdm(M) == minAdm(sorted M) for all M? ----
breaks=[]
checked=0
for L in range(2,6):            # lengths 2..5 (widths L)
    for M in product(range(0,5), repeat=L):
        checked+=1
        if minAdm(M) != minAdm(tuple(sorted(M))):
            breaks.append((M, minAdm(M), tuple(sorted(M)), minAdm(tuple(sorted(M)))))
print(f"[full-sort perm-invariance] checked {checked} vectors (entries 0..4, len 2..5)")
if breaks:
    print(f"  ★ REFUTED: {len(breaks)} breaks. First 8:")
    for (M,vM,sM,vsM) in breaks[:8]:
        print(f"    M={M} minAdm={vM}  vs sort={sM} minAdm={vsM}   Δ={vM-vsM}")
else:
    print("  NO break — minAdm(M) == minAdm(sort M) on the entire sweep (perm-invariance HOLDS here).")

# ---- also test FULL permutation-invariance (any permutation, not just sort) ----
breaks2=[]
for L in range(2,5):
    for M in product(range(0,5), repeat=L):
        base=minAdm(M)
        for P in set(permutations(M)):
            if minAdm(P)!=base:
                breaks2.append((M,P,base,minAdm(P))); break
print(f"[any-permutation] len 2..4, entries 0..4: {'NO break — fully perm-invariant' if not breaks2 else f'{len(breaks2)} breaks e.g. '+str(breaks2[0])}")
