"""
Reliable exact-N: is the DRAFT's hpiv-gated codim-uρ bare-constant route SOUND?
Condition: with corank ab/2 extracted (strong-block, hcvg) leaving c''=c'-ab/2 for the P-block,
D-B needs c'' < uρ/2, i.e. c' < (ab + uρ)/2. This reaches c'<1/2minAdm(M) IFF minAdm(M) <= ab + uρ.
Since hpiv: minAdm(redChain u M) <= u*rho, and cut-soundness: minAdm(M) <= ab + minAdm(redChain u M),
=> minAdm(M) <= ab + u*rho whenever hpiv holds. CONFIRM over interior (hcvg) hpiv-cells. rho=tailMinWidth.
NO MC.
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
interior_hpiv=0; sound_fail=0; ex=[]
for arity in (4,5):
    for M in product(range(1,WMAX+1),repeat=arity):
        M0,M1=M[0],M[1]
        rho=min(M[1:])          # tailMinWidth = min(M1..Mlast)
        for u in range(1,min(M0,M1)+1):
            a=M0-u; b=M1-u
            rc=redChain(u,M)
            hpiv = (minAdm(rc) <= u*rho)
            # interior: exists (t,j) with u=t+j and a+b<=m=min(M1,Mlast)-j; use j=0 rep (m=min(M1,Mlast))
            m = min(M1, M[-1])
            interior = (a+b <= m)
            if not (interior and hpiv): continue
            interior_hpiv+=1
            # draft soundness: minAdm(M) <= ab + u*rho
            if not (minAdm(M) <= a*b + u*rho):
                sound_fail+=1
                if len(ex)<6: ex.append((M,u,a,b,rho,minAdm(M),a*b+u*rho))
print(f"interior (a+b<=m) hpiv-true cuts (arity 4,5, widths<= {WMAX}): {interior_hpiv}")
print(f"  draft-route soundness FAILS (minAdm(M) > ab+uρ): {sound_fail}  (expect 0)")
for e in ex: print("   fail (M,u,a,b,rho,minAdm,ab+uρ):",e)
print("  => draft codim-uρ bare-constant route SOUND (reaches 1/2minAdm) whenever hpiv holds" if sound_fail==0 else "  => RECHECK")
