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
def clsCodim(M0,M1,M2eff,u,l,s):
    b=M1-u; d=M2eff-b
    return u*b + M0*l + (M0-s)*(u-l-s) + s*(d-l)
def leafmin(M0,M1,rho,u):
    b=M1-u;best=None
    for l in range(0,u+1):
        for s in range(0,u+1):
            if l+s<=u and b+l<=rho and u-l-s>=0:
                c=clsCodim(M0,M1,rho,u,l,s)
                if best is None or c<best:best=c
    return best

# For arity>=4 strict-shell binding cuts: gap = leaf min C_{l,s}(rho) - (minAdm - ab).
# leaf gate proves >=0 (clsCodim_gate_genL). gap>0 => leaf charts UNDER-COUNT => tail-drop strata needed.
rows=[]
maxw=6
for ar in range(4,6):
    for M in iproduct(range(1,maxw+1),repeat=ar):
        if M[0]<1 or M[1]<1: continue
        tstar,mA=binding_cut(M)
        r=min(M[0]-tstar,M[1]-tstar)
        for j in range(1,r):
            u=tstar+j;a=M[0]-u;b=M[1]-u
            if a<1 or b<1: continue
            rho=deepTailMin(M)
            if b>rho: continue
            ab=a*b; lm=leafmin(M[0],M[1],rho,u)
            gap=lm-(mA-ab)
            rows.append((gap, M,u,a,b,rho,mA,ab,lm))
rows.sort(reverse=True)
gaps=[g for g,*_ in rows]
import statistics
print(f"arity>=4 strict-shell cuts: {len(rows)}")
print(f"gap = leafmin - (minAdm-ab):  min={min(gaps)} max={max(gaps)}  #gap>0={sum(1 for g in gaps if g>0)}  #gap==0={sum(1 for g in gaps if g==0)}  #gap<0={sum(1 for g in gaps if g<0)}")
print("largest gaps (leaf charts under-count the most => biggest missing tail-drop strata):")
for g,M,u,a,b,rho,mA,ab,lm in rows[:10]:
    print(f"  gap={g}  M={M} u={u} a={a} b={b} rho={rho}  minAdm={mA} ab={ab} leafmin={lm}  minAdm-ab={mA-ab}")
print("... and the M2>rho (interior narrow) subset (deepTailMin<M2), where leaf uses rho not M2:")
cnt=0
for g,M,u,a,b,rho,mA,ab,lm in rows:
    if rho<M[2] and cnt<6:
        print(f"  gap={g} M={M} u={u} a={a} b={b} rho={rho}(<M2={M[2]}) minAdm-ab={mA-ab} leafmin={lm}"); cnt+=1
