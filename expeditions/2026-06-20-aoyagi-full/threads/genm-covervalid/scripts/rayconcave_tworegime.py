# Two-regime proof skeleton for concavity of D_M(x)=minAdm((x,M2,...,Mlast)), taillen>=2.
# g(x,s)=(x-s)(M2-s)+E(s), E(s)=minAdm((s,)+T') [= D_{tail}(s), concave by IH], domain s<=min(x,M2).
# Regimes: BOUNDARY B={x: D(x)=E(x)} (full-pivot optimal, smax(x)=x); INTERIOR = complement.
# Claims to verify (0 fails => clean formalizable skeleton):
#  (P1) B is an initial interval [0,x0].
#  (P2) INTERIOR x (x>x0): smin(x) <= x-1  (anchor midpoint proof: s=smin(x) feasible at x-1,x,x+1).
#  (P3) MIDPOINT via anchor: for x>=1 with smin(x)<=x-1: D(x-1)+D(x+1) <= 2 D(x). (affine-in-x at fixed s)
#  (P4) SEAM/within-B: for x>=1 with D(x)=E(x) AND D(x-1)=E(x-1): concavity Δ(x)<=Δ(x-1) holds,
#       and it reduces to E's concavity on the E-part + a single seam step.
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def Dfun(tail,x): return minAdm((x,)+tuple(tail))
def Efun(tail,x): return minAdm((x,)+tuple(tail[1:]))       # E(x)=D_{tail}(x)
def argmins(tail,x):
    M2=tail[0]; Tp=tail[1:]
    c=[(s,(x-s)*(M2-s)+minAdm((s,)+tuple(Tp))) for s in range(min(x,M2)+1)]
    m=min(v for _,v in c); return [s for s,v in c if v==m]

XMAX=12
p1_fail=0; p2_fail=0; p3_fail=0; seam_fail=0
covered=0; total_x=0
for taillen in range(2,5):
    for tail in product(range(1,7),repeat=taillen):
        B=[x for x in range(0,XMAX+2) if Dfun(tail,x)==Efun(tail,x)]
        # (P1) B initial interval
        if B != list(range(0, (max(B)+1) if B else 0)):
            p1_fail+=1
        x0 = max(B) if B else -1
        for x in range(1,XMAX):
            total_x+=1
            smin=min(argmins(tail,x))
            inB = (Dfun(tail,x)==Efun(tail,x))
            # (P2) interior => smin<=x-1
            if not inB and smin>x-1: p2_fail+=1
            # (P3) anchor midpoint when smin<=x-1
            if smin<=x-1:
                covered+=1
                if not (Dfun(tail,x-1)+Dfun(tail,x+1) <= 2*Dfun(tail,x)): p3_fail+=1
            else:
                # smin=x (forced boundary). Then need D(x-1)=E(x-1) and the seam.
                if Dfun(tail,x-1)!=Efun(tail,x-1): seam_fail+=1   # x-1 also in B?
                # concavity direct at this seam x:
                if not (Dfun(tail,x+1)-Dfun(tail,x) <= Dfun(tail,x)-Dfun(tail,x-1)): seam_fail+=1
print(f"(P1) B not an initial interval: {p1_fail}")
print(f"(P2) interior x with smin(x)>x-1: {p2_fail}")
print(f"(P3) anchor-midpoint failures (smin<=x-1): {p3_fail}   [covers {covered}/{total_x} of x's]")
print(f"(P4) seam (smin(x)=x): x-1 not in B OR concavity fails: {seam_fail}")
# Characterize the seam step cleanly: when smin(x)=x, what closes Δ(x)<=Δ(x-1)?
# candidate: Δ(x) <= 0  (D flat/decreasing there) since full-pivot saturating?  test:
seam_delta=[]
for taillen in range(2,4):
    for tail in product(range(1,6),repeat=taillen):
        for x in range(1,XMAX):
            if min(argmins(tail,x))==x:
                dx=Dfun(tail,x+1)-Dfun(tail,x); dxm=Dfun(tail,x)-Dfun(tail,x-1)
                seam_delta.append((dx,dxm))
import statistics
print(f"seam cases sampled: {len(seam_delta)}; all Δ(x)<=Δ(x-1): {all(a<=b for a,b in seam_delta)}; "
      f"Δ(x-1) range {min(b for _,b in seam_delta)}..{max(b for _,b in seam_delta)}")
