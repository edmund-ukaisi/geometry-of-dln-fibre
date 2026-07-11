"""
Binding-cut diagnostic for the db2 single-branch model
    lambda = n1/2 + (1/2) min(n0, D/m),   full = (1/2)(n0+n1) = (1/2)minAdm  iff  D/m >= n0.
At the FRONT-PEEL binding cut t*:  a=M0-t*, b=M1-t*, n0=ab, n1=minAdm(redChain(t*)),
so n0+n1 = minAdm(M) (binding).  m=1 (radical determinantal + Cauchy-Binet: U0=sigma_min^2 ~ dist^2).
D = codim of the deeper-product rank drop that de-ranks the b corank rows: {rank(deeper) <= b-1}.
Candidate deeper products:
  D_A = cCodim((M2,...,ML); b-1)                 [Zdeep = A2...A_L, single/prod, rank<=b-1]
  D_B = cCodim((b, M2,...,ML); b-1)              [corank block W = A1cor . Zdeep, chain (b,M2..ML)]
  D_C = cCodim((t*, M2,...,ML); b-1)             [redChain-leading pivot form]
We check which candidate makes  n1/2 + (1/2)min(n0, D) == (1/2)minAdm, and whether D >= n0.
"""
from functools import lru_cache
import itertools

@lru_cache(None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

@lru_cache(None)
def cCodim(c, rho):
    c=tuple(c); L=len(c)-1
    if L==0: return 0
    if L==1:
        r=min(rho,c[0],c[1]); return (c[0]-r)*(c[1]-r)
    best=None; rng=range(0,max(c)+1)
    for T in itertools.product(rng,repeat=L):
        if any(T[i]<T[i+1] for i in range(L-1)): continue
        if T[0]>min(c[0],c[1]): continue
        if T[-1]>rho: continue
        if not all(T[j]<=min(T[j-1],c[j+1]) for j in range(1,L)): continue
        val=(c[0]-T[0])*(c[1]-T[0])+sum((T[j-1]-T[j])*(c[j+1]-T[j]) for j in range(1,L))
        if best is None or val<best: best=val
    return best if best is not None else 0

def binding_cuts(M):
    M=tuple(M); ma=minAdm(M); cuts=[]
    for t in range(min(M[0],M[1])+1):
        if (M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:])==ma: cuts.append(t)
    return cuts

def half(x): return x/2

sweep=[(3,3,3,4),(3,5,2,5),(2,4,2,5),(2,4,4,5),(2,5,2,2,5),(4,4,4,4),(5,5,5,5),
       (2,5,5,5),(5,5,5,2),(3,3,3,3,4),(4,4,4,4,4),(2,4,4,4,5),(3,3,2,2),(4,3,3,4),
       (2,4,3,5),(3,4,5,4,3),(5,2,5),(5,2,2,5),(6,2,6),(7,2,2,2,7),(2,6,2,6,2),(3,6,3),(4,2,4,2,4)]

print("="*118)
print("BINDING-CUT db2 CHECK:  n1/2 + 1/2 min(n0, D) =?= 1/2 minAdm   [m=1];  and is D >= n0 (no min bite)?")
print("="*118)
worst=[]
for M in sweep:
    M=tuple(M); ma=minAdm(M)
    for t in binding_cuts(M):
        a=M[0]-t; b=M[1]-t; n0=a*b
        red=(t,)+M[2:]; n1=minAdm(red)
        if b<1:   # degenerate (empty corank block): p=0 vacuous, no coupled corner
            print(f"M={str(M):15} t*={t}: a={a} b={b} n0={n0} (b<1: NO decorated corner, vacuous)")
            continue
        deeper=M[2:]
        D_A=cCodim(deeper,b-1)
        D_B=cCodim((b,)+deeper,b-1)
        D_C=cCodim((t,)+deeper,b-1) if t>=1 else None
        def lam(D): return half(n1)+half(min(n0,D))
        okA=abs(lam(D_A)-half(ma))<1e-9
        okB=abs(lam(D_B)-half(ma))<1e-9
        # report
        tag=""
        if D_A<n0: tag+=" D_A<n0"
        if D_B<n0: tag+=" D_B<n0"
        print(f"M={str(M):15} t*={t}: a={a} b={b} n0=ab={n0:2} n1={n1:2} (n0+n1={n0+n1}=minAdm={ma}) | "
              f"D_A(deeper;b-1)={D_A:2} D_B((b,deeper);b-1)={D_B:2} | lamA={lam(D_A)} lamB={lam(D_B)} halfminAdm={half(ma)} | okA={okA} okB={okB}{tag}")
        if not (okA or okB): worst.append((M,t))
print()
print("Chains where NEITHER D_A nor D_B reproduces 1/2 minAdm:", worst if worst else "NONE")
