from itertools import product
from functools import lru_cache
def redchain(t,M): return (t,)+tuple(M[2:])
@lru_cache(maxsize=None)
def minadm(M):
    n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minadm(redchain(t,M)) for t in range(min(M[0],M[1])+1))
def argmin_t(M):
    best=None;bt=None
    for t in range(min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minadm(redchain(t,M))
        if best is None or v<best: best=v;bt=t
    return bt

pure_scope_fail=0; hcvg_fail=0; both0=0; oneonly=0; tot=0
ex_scope=[]
for nw in (3,4,5):
    for M in product(range(1,7),repeat=nw):
        M=tuple(M); ts=argmin_t(M); r=min(M[0]-ts,M[1]-ts)
        if r<1: continue
        j=r; u=ts+j; a=M[0]-u; b=M[1]-u; tot+=1
        if a==0 and b==0: both0+=1
        else: oneonly+=1
        # pure incidence scope a+b<=M2
        if not (a+b<=M[2]):
            pure_scope_fail+=1
            if len(ex_scope)<4: ex_scope.append((M,a,b,"a+b=%d M2=%d"%(a+b,M[2])))
        # codebase hcvg (stronger)
        Mlast=M[-1]
        if not (a+b <= min(M[1],Mlast)-j and min(M[1],Mlast)-j<=M[2]): hcvg_fail+=1
print("j=r cuts total:",tot)
print(" both a=b=0 (M0=M1):",both0,"  exactly one zero:",oneonly)
print(" pure incidence scope a+b<=M2 FAILS:",pure_scope_fail, ex_scope)
print(" codebase hcvg+hrange FAILS:",hcvg_fail," (stronger than a+b<=M2)")
# minAdm(M)<=minAdm(R) from recursion candidate t=u (ab=0): direct, verify a couple
for M in [(6,1,1),(2,1,2),(4,4,4,4),(5,3,2,6)]:
    ts=argmin_t(M); r=min(M[0]-ts,M[1]-ts); u=ts+r
    R=redchain(u,M); ab=(M[0]-u)*(M[1]-u)
    print(f"  M={M}: u={u} ab={ab} minAdm(M)={minadm(M)} <= ab+minAdm(R)={ab+minadm(R)} (=minAdm(R)={minadm(R)})", minadm(M)<=minadm(R))
