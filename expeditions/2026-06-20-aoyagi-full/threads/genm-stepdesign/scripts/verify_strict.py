from functools import lru_cache
from itertools import product as iproduct
@lru_cache(None)
def minAdm(M):
    if len(M)==2: return M[0]*M[1]
    M0,M1=M[0],M[1]
    return min((M0-t)*(M1-t)+minAdm((t,)+M[2:]) for t in range(0,min(M0,M1)+1))
def binding_cut(M):
    M0,M1=M[0],M[1];best=None;arg=None
    for t in range(0,min(M0,M1)+1):
        v=(M0-t)*(M1-t)+minAdm((t,)+M[2:])
        if best is None or v<best: best=v;arg=t
    return arg,best
def deepTailMin(M): return min(M[2:])
def clsCodim(M0,M1,rho,u,l,s):
    b=M1-u; d=rho-b; return u*b+M0*l+(M0-s)*(u-l-s)+s*(d-l)
def leafmin(M0,M1,rho,u):
    b=M1-u;best=None
    for l in range(0,u+1):
        for s in range(0,u+1):
            if l+s<=u and b+l<=rho and u-l-s>=0:
                c=clsCodim(M0,M1,rho,u,l,s); best=c if best is None else min(best,c)
    return best
# smallest genuine strict-shell (r>=2) arity>=4 with gap>0
cands=[]
for ar in range(4,6):
    for M in iproduct(range(1,7),repeat=ar):
        tstar,mA=binding_cut(M); r=min(M[0]-tstar,M[1]-tstar)
        for j in range(1,r):
            u=tstar+j;a=M[0]-u;b=M[1]-u
            if a<1 or b<1: continue
            rho=deepTailMin(M)
            if b>rho: continue
            lm=leafmin(M[0],M[1],rho,u); gap=lm-(mA-a*b)
            if gap>0: cands.append((sum(M),M,tstar,r,u,a,b,rho,mA,a*b,lm,gap))
cands.sort()
print("smallest genuine strict-shell (1<=j<r, r>=2) arity>=4 cuts with gap>0:")
for tot,M,tstar,r,u,a,b,rho,mA,ab,lm,gap in cands[:8]:
    print(f"  M={M} t*={tstar} r={r} u={u}(strict j={u-tstar}) a={a} b={b} rho={rho} | minAdm={mA} ab={ab} floor(minAdm-ab)={mA-ab} leafmin={lm} GAP={gap}")
print(f"total gap>0 strict-shell cuts: {len(cands)}")
