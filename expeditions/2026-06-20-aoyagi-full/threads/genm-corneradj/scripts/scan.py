from functools import lru_cache
import itertools
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    best=None
    for t in range(min(M[0],M[1])+1):
        red=(t,)+M[2:]; val=(M[0]-t)*(M[1]-t)+minAdm(red)
        best=val if best is None else min(best,val)
    return best
# scan chains length 3 and 4, widths 1..6. Find BINDING cuts t (ab+minAdm(red)=minAdm(M)) that are at the EDGE
# a+b = tailMinWidth+1, with a,b>=1 (nontrivial), i.e. rho=a+b-1.
def tailmin(M): return min(M[1:])
hits=0; checked=0
for Lp in [3,4]:
    for M in itertools.product(range(1,7),repeat=Lp):
        checked+=1
        mA=minAdm(M); rho=tailmin(M)
        for t in range(1,min(M[0],M[1])+1):
            a,b=M[0]-t,M[1]-t
            if a<1 or b<1: continue
            red=(t,)+M[2:]
            binding = (a*b+minAdm(red)==mA)
            edge = (a+b==rho+1)
            if binding and edge:
                hits+=1
                if hits<=15: print(f"EDGE@BINDING: M={M} t={t} a={a} b={b} rho={rho} minAdm={mA} ab+red={a*b+minAdm(red)}")
print(f"checked {checked} chains; edge-at-binding-cut hits = {hits}")
# also: is edge EVER at binding for a=b=2 specifically? and report min chain
