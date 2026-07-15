from functools import lru_cache
from itertools import product as iproduct

@lru_cache(maxsize=None)
def CR(widths,s):
    v=tuple(widths)
    if len(v)==2:
        v0,v1=v
        return 0 if s>=min(v0,v1) else (v0-s)*(v1-s)
    vpm1,vp=v[-2],v[-1]; best=None
    for r in range(0,min(vpm1,vp)+1):
        val=(vpm1-r)*(vp-r)+(0 if r<=s else CR(v[:-2]+(r,),s))
        if best is None or val<best: best=val
    return best

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    m0,m1=M[0],M[1]; rest=M[2:]; best=None
    for t in range(0,min(m0,m1)+1):
        val=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or val<best: best=val
    return best

def gamma(a,b,s):
    lo=max(0,b-s); return max((h*(a+b-s-h) for h in range(lo,b+1)), default=0)

def bindingcut(M):
    # t* = argmin f(t)=(M0-t)(M1-t)+minAdm(redChain t M); redChain t M = (t, M2, ..., Mlast)
    m0,m1=M[0],M[1]; rest=M[2:]; best=None; targ=None
    for t in range(0,min(m0,m1)+1):
        val=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or val<best: best=val; targ=t
    return targ

# GATE CHECK: at binding strict shells, C_k >= minAdm(M)-ab for all k, AND kappa_k >= binom(k+1,2)
print("=== deep-stratum gate C_k >= minAdm(M)-ab (binding strict shells) + kappa vs gamma ===")
viol=0; kg_viol=0; ntot=0
for arity in range(4,7):
  for M in iproduct(range(1,7), repeat=arity):
    tstar=bindingcut(M); m0,m1=M[0],M[1]
    r=min(m0-tstar,m1-tstar)
    deep=M[2:]; rho=min(deep); n=M[-1]
    for j in range(1,r):  # strict shell 1<=j<r
        u=tstar+j; a=m0-u; b=m1-u
        if a<1 or b<1: continue
        ntot+=1
        target=minAdm(M)-a*b
        for k in range(1,rho+1):
            s=rho-k
            kappa=CR(deep,k and rho-k or rho-k)  # CR(deep, rho-k)
            kappa=CR(deep,rho-k)
            g=gamma(a,b,s)
            Ck=min(u*rho, u*(rho-k)+kappa-g)
            if Ck<target: viol+=1
            # kappa >= binom(k+1,2) and gamma<=floor((a+b-s)^2/4)
            if kappa < k*(k+1)//2: kg_viol+=1
print(f"  strict-shell binding cuts tested: {ntot}")
print(f"  C_k < minAdm(M)-ab violations: {viol}")
print(f"  kappa_k < binom(k+1,2) violations: {kg_viol}")

# also confirm full-collapse: minAdm(deep) >= minAdm(M)
fc=0; fctot=0
for arity in range(4,7):
  for M in iproduct(range(1,7),repeat=arity):
    fctot+=1
    if minAdm(M[2:]) < minAdm(M): fc+=1
print(f"  minAdm(deep) < minAdm(M) violations: {fc} / {fctot}")
