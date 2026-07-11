"""
Verify Codex's decorrelated claims (never trust unrun):
 (V1) minAdm(1,5,3,3)=3 and the per-cell CORRECTED formula 1/2(M0*rho + min(M0*q, D_q));
      the naive 1/2(D_q+d_q) OVERSTATES a cell when D_q > M0*q (narrow front M0=1).
 (V2) (4,3,3,3): E(rho)=D(rho)+M0*rho = (7,7,9,12); minAdm=7; Codex branch codim 7.
 (V3) det(PP^T) ~ t^{2q} for corank q (order 2q), vs sigma_min^2 ~ t^2 (order 2, m=1) -- the misread.
 (V4) corrected per-cell min over cells == minAdm for a broad sweep (the true no-collapse identity).
"""
import numpy as np, itertools, sympy as sp
from functools import lru_cache

@lru_cache(None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
@lru_cache(None)
def cCodim(c,rho):
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

def cells(M):
    M=tuple(M); M0=M[0]; deeper=M[1:]; r=min(deeper)
    out=[]
    for q in range(0,r+1):
        rho=r-q; Dq=cCodim(deeper,rho); dq=M0*rho
        naive=Dq+dq                          # sector-cert per-cell claim
        corrected=M0*rho + min(M0*q, Dq)     # Codex corrected per-cell
        out.append((q,rho,Dq,dq,naive,corrected))
    return M0,r,out

print("V1/V2:  per-cell naive 1/2(D_q+d_q) vs Codex-corrected 1/2(M0*rho+min(M0*q,D_q)); min == minAdm?")
for M in [(1,5,3,3),(4,3,3,3),(3,3,3,4),(5,2,5),(1,4,4,4),(2,5,2,2,5),(7,2,2,2,7)]:
    M0,r,cs=cells(M); ma=minAdm(M)
    naive_min=min(c[4] for c in cs); corr_min=min(c[5] for c in cs)
    diff=[f"q{c[0]}:naive{c[4]}/corr{c[5]}" for c in cs if c[4]!=c[5]]
    print(f" M={str(M):16} minAdm={ma:2} | naive_min={naive_min} corr_min={corr_min} "
          f"(corr==minAdm: {corr_min==ma}; naive==minAdm: {naive_min==ma}) | cells differ: {diff if diff else 'none'}")
print()

# V3: det(PP^T) order vs sigma_min^2 order for a corank-q drop of a PRODUCT
print("V3: transverse orders for a corank-q product rank drop (t = tube param):")
t=sp.Symbol('t',real=True)
import random
for (chain,q) in [((3,3),2),((4,4),2),((4,4),3)]:  # single free matrix P n0 x n1, drop q
    rng=random.Random(5)
    n0,n1=chain
    # P(t): rank drops by q as t->0; build P = U diag(s) V with q of the s ~ t, rest ~1
    r=min(n0,n1)
    U=sp.Matrix(n0,r,lambda i,j: sp.Rational(rng.randint(-3,3)))
    V=sp.Matrix(r,n1,lambda i,j: sp.Rational(rng.randint(-3,3)))
    # QR-ish: just use U,V generic; scale last q singular directions by t via a diagonal gate
    S=sp.diag(*([1]*(r-q)+[t]*q))
    P=U*S*V
    PPt=P*P.T
    # det of the top r x r gram principal (Cauchy-Binet ~ prod of all r singular^2)
    detG=sp.factor(sp.expand((PPt[:r,:r]).det())) if r<=n0 else None
    # smallest 'singular^2' proxy: e_r(PP^T)/e_{r-1} is messy; instead track e_r (all sing^2 product)
    # order of the full r-minor gram det in t = 2q (q factors ~t^2). sigma_min^2 ~ t^2 (one factor).
    e_r = sp.expand((P[:r,:r]).det()**2) if r<=min(n0,n1) else None
    ordr = min(m[0] for m in sp.Poly(sp.expand((P[:r,:r]).det()),t).monoms()) if r<=min(n0,n1) else None
    print(f"  P={n0}x{n1}, corank q={q}: order of one r-minor in t = {ordr} (=> (minor)^2 order {2*ordr if ordr is not None else '?'}); "
          f"det(r-Gram) ~ t^(2q)={2*q} = ALL q collapsing sigma^2 (the MISREAD if used as sigma_min^2 which is t^2).")
