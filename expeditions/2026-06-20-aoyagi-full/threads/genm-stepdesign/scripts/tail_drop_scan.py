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

def clsCodim(M0,M1,M2,u,l,s):
    b=M1-u; d=M2-b
    return u*b + M0*l + (M0-s)*(u-l-s) + s*(d-l)

def strata(M0,M1,M2,u):
    b=M1-u;d=M2-b;out=[]
    for l in range(0,u+1):
        for s in range(0,u+1):
            if l+s<=u and b+l<=M2 and u-l-s>=0:
                out.append((l,s,clsCodim(M0,M1,M2,u,l,s)))
    return out

# tail-drop-k stratum codim (Codex model, worst-case square bottleneck kappa_k = k^2):
#   C_{l,s}(rho) - k*s + k^2 ,  using effective rho=deepTailMin. Here M2 in clsCodim is replaced by
#   the EFFECTIVE deep width rho (since the leaf reduction is to rho). We use rho in place of M2.
def scan(maxw=6, maxar=5, kappa='sq'):
    walls=[];checked=0
    widths=range(1,maxw+1)
    for ar in range(3,maxar+1):
        for M in iproduct(widths, repeat=ar):
            if M[0]<1 or M[1]<1: continue
            tstar,mA=binding_cut(M)
            r=min(M[0]-tstar,M[1]-tstar)
            for j in range(1,r):  # STRICT shell 1<=j<r
                u=tstar+j
                a=M[0]-u; b=M[1]-u
                if a<1 or b<1: continue
                rho=deepTailMin(M)
                if b>rho: continue  # corank can't survive; out of scope
                ab=a*b
                claimT = mA - ab            # 2*T1_q claimed by capstone
                # leaf strata using EFFECTIVE width rho (not M2)
                st = strata(M[0],M[1],rho,u)
                if not st: continue
                leafmin=min(c for (_,_,c) in st)
                # tail-drop min over k>=1, using kappa_k = k^2 (worst case square bottleneck)
                tdmin=None
                for (l,s,c) in st:
                    for k in range(1, rho+1):
                        if rho-k < b: break   # deeper drop kills corank (separate charge issue); stop
                        kap = k*k if kappa=='sq' else k
                        cand = c - k*s + kap
                        if tdmin is None or cand<tdmin: tdmin=cand
                overall = min(leafmin, tdmin) if tdmin is not None else leafmin
                checked+=1
                if overall < claimT:
                    walls.append((M,u,a,b,rho,ab,claimT,leafmin,tdmin,overall))
    return walls,checked

for kap in ['sq','lin']:
    walls,checked=scan(kappa=kap)
    print(f"kappa_k={'k^2' if kap=='sq' else 'k (aggressive/unphysical)'}: strict-shell cuts checked={checked}, WALLS (overall<minAdm-ab)={len(walls)}")
    for w in walls[:12]:
        M,u,a,b,rho,ab,claimT,leafmin,tdmin,overall=w
        print(f"  M={M} u={u} a={a} b={b} rho={rho}: minAdm-ab={claimT} leafmin={leafmin} tail-drop-min={tdmin} OVERALL={overall}")
