from functools import lru_cache
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
# Census: which charts (t) in the peel sum have a >= minAdm(M) (so c' < ½minAdm < a/2 ALWAYS -> atom
# INAPPLICABLE, must use the bounded-integrand c'<=a/2 branch). t ranges 1..min(M0,M1).
print("charts where atom (needs c'>a/2) is NEVER applicable for c'<½minAdm(M)  [a >= minAdm(M)]:")
found=0; total=0
import itertools
for widths in itertools.product(range(1,5),repeat=4):
    M=tuple(widths)
    if len(M)<3: continue
    mm=minAdm(M)
    for t in range(1,min(M[0],M[1])+1):
        a=(M[0]-t)*(M[1]-t); total+=1
        if a>=mm and mm>0:
            found+=1
            if found<=6: print(f"   M={M} t={t}: a={a} >= minAdm={mm}  => c'<{mm/2} < a/2={a/2}  (atom inapplicable)")
print(f"   ...{found}/{total} (t>=1) charts over width-1..4 4-chains are atom-INAPPLICABLE  => c'<=a/2 branch is REAL")
