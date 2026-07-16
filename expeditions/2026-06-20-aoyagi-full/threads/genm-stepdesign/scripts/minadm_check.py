from functools import lru_cache
from itertools import product

@lru_cache(None)
def minAdm(M):
    # M tuple of widths, len>=2. leaf: len==2 -> M0*M1
    if len(M)==2: return M[0]*M[1]
    M0,M1=M[0],M[1]
    tail=M[1:]  # (M1,...)
    best=None
    for t in range(0,min(M0,M1)+1):
        red=(t,)+M[2:]   # redChain t M = (t, M2, ..., last)
        val=(M0-t)*(M1-t)+minAdm(red)
        if best is None or val<best: best=val
    return best

def binding_cut(M):
    M0,M1=M[0],M[1]
    best=None;arg=None
    for t in range(0,min(M0,M1)+1):
        red=(t,)+M[2:]
        val=(M0-t)*(M1-t)+minAdm(red)
        if best is None or val<best: best=val;arg=t
    return arg,best

def deepTailMin(M): return min(M[2:])  # min over indices>=2

def clsCodim(M0,M1,M2,u,l,s):
    b=M1-u; d=M2-b
    return u*b + M0*l + (M0-s)*(u-l-s) + s*(d-l)

def min_cls(M0,M1,M2,u):
    b=M1-u; d=M2-b
    best=None
    for l in range(0,u+1):
        for s in range(0,u+1):
            if l+s<=u and b+l<=M2 and s<=u:
                # feasibility as in cert: s<=u-l ok; also need u-l-s>=0 (in the factor) -> ensure valid
                c=clsCodim(M0,M1,M2,u,l,s)
                if best is None or c<best: best=c
    return best

# M=(3,3,3,3)
M=(3,3,3,3)
print("minAdm(3,3,3,3)=",minAdm(M)," binding cut t*,val=",binding_cut(M)," deepTailMin=",deepTailMin(M))
tstar,_=binding_cut(M)
print(" r = min(M0-t*,M1-t*) =",min(M[0]-tstar,M[1]-tstar))
# at u=2: a=1,b=1,rho=deepTailMin=3
u=2;a=M[0]-u;b=M[1]-u;rho=deepTailMin(M);ab=a*b
minC=min_cls(M[0],M[1],M[2],u)
T1=minAdm(M)/2
T1q=T1-ab/2
print(f" u={u} a={a} b={b} rho={rho} ab={ab}")
print(f" min C_ls (leaf) = {minC}   leaf-gate q<minC/2 = {minC/2}")
print(f" minAdm={minAdm(M)}  T1=minAdm/2={T1}  ACTUAL q-bound T1q=T1-ab/2 = {T1q}")
print(f" Codex tail-drop gate: 2q < u*rho-u+kappa = {u*rho-u+1}, i.e. q < {(u*rho-u+1)/2}  (kappa=1)")
print(f" Codex counterexample q=11/4={11/4}: in leaf-gate(q<{minC/2})? {11/4<minC/2};  in ACTUAL scope(q<{T1q})? {11/4<T1q}")
