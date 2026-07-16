"""
Reliable exact-N check: does the EDGE COUPLED descent (edgefub's hBackbone) reach 1/2minAdm(M)
via the CLEAN pointwise density fold (=> NO tie-log), or do some b=1 edge cells need the joint
rank-sector (=> a log/delta-slack)?

After edgefub's leaf + radial collapse the front factor is frobSq(P.Qt) = frobSq(z~0 . Z_deep),
z~0 = X.Y, X=[P|B12] (u x M1, full row rank u), Y=[z0;A_cor] (M1 x M2) -- satred's X.Y pushforward,
now at the SHIFTED exponent c'' = c' - a/2 (b=1: peelCharge/2 = a*b/2 = a/2).

Pointwise density fold: rho(z~0) <= K * frobSq(...)^{-A/2}, A = satred density order
   A = max_{1<=j<=min(u,M2)} j*(M2 - b - j)   (b=1: j*(M2-1-j))
=> reduction reaches c'<1/2minAdm(M) via RMBTF(redChain u M)(c''+A/2) IFF
   c''+A/2 < 1/2 minAdm(redChain)  for all c'<1/2minAdm(M)
   <=> A <= 2*Delta + a,  2*Delta = minAdm(redChain u M) - minAdm(M),  a = M0-u.
If A <= 2Delta+a for ALL b=1 a<u edge cuts  => coupled route is CLEAN (no tie-log). Verify.
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

def densityA(u,b,M2):
    # satred density order for X.Y pushforward, X full-row-rank u, corank width b
    best=0
    for j in range(1,min(u,M2)+1):
        best=max(best, j*(M2-b-j))
    return best

WMAX=7
cells=0; undershoot=0; marginal=0; ex_under=[]; ex_marg=[]
for arity in (4,5):
    for M in product(range(1,WMAX+1),repeat=arity):
        M0,M1,M2=M[0],M[1],M[2]
        # b=1 cut: u = M1-1  (needs u>=1 and u<=min(M0,M1))
        u=M1-1
        if u<1 or u>min(M0,M1): continue
        b=M1-u  # =1
        a=M0-u
        if a<1: continue        # need corank a>=1 (edge, not saturated)
        if not (a<u): continue  # edgefub scope: a<u strict
        rc=redChain(u,M); mRC=minAdm(rc); mM=minAdm(M)
        twoDelta=mRC-mM
        A=densityA(u,b,M2)
        cells+=1
        if A > twoDelta + a:
            undershoot+=1
            if len(ex_under)<8: ex_under.append((M,u,a,b,M2,A,twoDelta,a, twoDelta+a))
        elif A == twoDelta + a:
            marginal+=1
            if len(ex_marg)<5: ex_marg.append((M,u,a,A,twoDelta+a))
print(f"b=1 a<u edge cuts scanned (arity 4,5, widths<= {WMAX}): {cells}")
print(f"pointwise-fold UNDERSHOOTS (A > 2Delta+a  => needs joint rank-sector / tie-log): {undershoot}")
print(f"MARGINAL (A = 2Delta+a, still reaches STRICTLY for c'<1/2minAdm): {marginal}")
if ex_under:
    print("  UNDERSHOOT examples (M,u,a,b,M2,A,2Delta,a,bound=2D+a):")
    for e in ex_under: print("   ",e)
else:
    print("  => 0 undershoot: the coupled route is CLEAN for ALL b=1 a<u edge cells (NO tie-log).")
for e in ex_marg[:3]: print("  marginal example (M,u,a,A,2D+a):",e)
