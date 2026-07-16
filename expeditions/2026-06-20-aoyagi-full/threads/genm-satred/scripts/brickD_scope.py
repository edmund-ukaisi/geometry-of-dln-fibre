"""
Reliable exact-N pin of Brick D's scope + per-arm boundaries (headSplit_domination,
RouteMSJDeeperFlagCore:513). NO MC. Checks:
 (1) cut-soundness minAdm(M) <= peelCharge(u) + minAdm(redChain u M)  [the shifted-exp gate]
 (2) the convergent-interior scope a+b<=m is STRICTLY-convergent (strongBlock a<m-b+1 holds,
     NO log) -- so the current statement's hcvg is the clean interior; the log-tie is a+b=m+1 (OUT).
 (3) in-scope cells (a+b<=m) are single-chain (k=a+b-rho <= 1): interior reduction suffices, reaches.
Widths (M0,M1,M2,...) <= WMAX, all binding cuts u=t+j, shell index j, m=min(M1,Mlast)-j.
"""
from functools import lru_cache
from itertools import product

def redChain(u, M): return (u,) + tuple(M[2:])
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm(redChain(t,M)) for t in range(min(M[0],M[1])+1))

WMAX=6
arities=[4,5]   # L+1+1+1 with L>=1  => arity>=4 (the box case)
n_cut=0; soundness_fail=0; interior_cells=0; log_tie_cells=0
interior_multichain_fail=0; scope_logconv_fail=0
examples_interior=[]; examples_tie=[]
for arity in arities:
    ranges=[range(1,WMAX+1)]*arity
    for M in product(*ranges):
        mM=minAdm(M)
        Mlast=M[-1]; rho=min(M[1:])            # tailMinWidth = min(M1,...,Mlast)
        # binding cuts: u = t+j, 1<=t<=min(M0,M1), 0<=j<=min(M0-t,M1-t); here iterate u directly
        for u in range(1, min(M[0],M[1])+1):
            a=M[0]-u; b=M[1]-u
            rc=redChain(u,M); mRC=minAdm(rc); peel=a*b
            # (1) cut-soundness
            if mM > peel + mRC: soundness_fail+=1
            n_cut+=1
            # scope m = min(M1,Mlast)-j.  For a cut u=t+j we don't fix j; use the SHELL scope test
            # against the widest feasible m at that corank: the corank-convergence hcvg is a+b<=m.
            # Take the representative m = min(M1,Mlast)-j; the shell index j = u - t, t>=1 => j<=u-1.
            for j in range(0, u):    # j = u - t, t=u-j >=1  => j in 0..u-1
                m = min(M[1], Mlast) - j
                if m < 0: continue
                inscope = (a+b <= m)          # hcvg
                if inscope:
                    interior_cells+=1
                    # strongBlock convergence a < m-b+1  (strict => NO log)
                    if not (a < m-b+1): scope_logconv_fail+=1
                    # single-chain? k=a+b-rho <=1
                    k=a+b-rho
                    if k>1:
                        interior_multichain_fail+=1
                        if len(examples_interior)<6: examples_interior.append((M,u,j,a,b,m,rho,k))
                elif a+b == m+1:
                    log_tie_cells+=1
                    if len(examples_tie)<6: examples_tie.append((M,u,j,a,b,m,rho))
print(f"cuts scanned: {n_cut}")
print(f"(1) cut-soundness fails (minAdm(M) > peel+minAdm(rc)): {soundness_fail}  (expect 0)")
print(f"(2) in-scope (a+b<=m) cells: {interior_cells}")
print(f"    of those, strongBlock a<m-b+1 FAILS (would log): {scope_logconv_fail}  (expect 0 => in-scope is clean, no log)")
print(f"(3) in-scope cells that are MULTI-chain (k=a+b-rho>1): {interior_multichain_fail}")
if examples_interior:
    print("    -> in-scope multi-chain examples (M,u,j,a,b,m,rho,k):")
    for e in examples_interior: print("      ",e)
print(f"    log-tie cells (a+b=m+1, OUT of scope): {log_tie_cells}")
for e in examples_tie[:3]: print("      tie example (M,u,j,a,b,m,rho):",e)
