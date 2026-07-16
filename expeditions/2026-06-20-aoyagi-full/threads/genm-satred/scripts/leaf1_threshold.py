"""
DECISIVE check (Codex leaf1 Q3): the shell gives sigma_m(G)>=eps, m=min(M1,Mlast)-j, so the front D-B is
UNIFORM iff 2c'' < u*m  (NOT u*rho). With c''=c'-ab/2 (corank extracted), reaching c'<1/2minAdm(M) needs
   minAdm(M) <= ab + u*m   (m = min(M1,Mlast)-j).
Verify over interior shells (hjr strict: 0<=j<min(M0-t,M1-t), cut u=t+j, t>=1). If it HOLDS everywhere,
route alpha is SAVED with the corrected u*m/2 threshold. If it FAILS, route alpha is broken for those cells
=> they need route-beta (carry det(GG^T) to IH). Compare vs the OLD (wrong) u*rho threshold. NO MC.
"""
from functools import lru_cache
from itertools import product
def redChain(u,M): return (u,)+tuple(M[2:])
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm(redChain(t,M)) for t in range(min(M[0],M[1])+1))
WMAX=7
shells=0; um_fail=0; urho_ok_but_um_fail=0; ex=[]
for arity in (4,5):
    for M in product(range(1,WMAX+1),repeat=arity):
        M0,M1,Mlast=M[0],M[1],M[-1]
        rho=min(M[1:])
        mM=minAdm(M)
        for t in range(1,min(M0,M1)+1):
            r=min(M0-t,M1-t)
            for j in range(0,r):          # hjr STRICT interior: j<r
                u=t+j; a=M0-u; b=M1-u
                m=min(M1,Mlast)-j
                shells+=1
                um_ok  = (mM <= a*b + u*m)
                urho_ok= (mM <= a*b + u*rho)
                if not um_ok:
                    um_fail+=1
                    if urho_ok and len(ex)<10: ex.append((M,t,j,u,a,b,m,rho,mM,a*b+u*m,a*b+u*rho))
print(f"interior shells (hjr strict, arity 4,5, widths<= {WMAX}): {shells}")
print(f"  um-threshold FAILS (minAdm(M) > ab+u*m) => route-alpha front bound INSUFFICIENT: {um_fail}")
print(f"  of those, the OLD u*rho threshold would have (wrongly) passed: {len(ex)} shown")
for e in ex: print("    (M,t,j,u,a,b,m,rho,minAdm,ab+um,ab+urho):",e)
if um_fail==0: print("  => route-alpha SAVED: minAdm(M)<=ab+um holds for ALL interior shells (um/2 threshold sufficient).")
else: print(f"  => route-alpha front bound INSUFFICIENT for {um_fail} shells (m<rho, um<needed) -> those need route-beta / carry det(GG^T) to IH.")
