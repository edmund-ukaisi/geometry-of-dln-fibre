from fractions import Fraction as F
def codim_r(M0,M1,M2,r): return (M0-r)*(M1-r)+r*M2
def minAdm3(M0,M1,M2):
    vals={r:codim_r(M0,M1,M2,r) for r in range(0,min(M0,M1)+1)}
    m=min(vals.values()); arg=min(r for r in vals if vals[r]==m); return m,arg,vals
def minAdm2(u,M2): return u*M2   # leaf 2-chain redChain = (u, M2)

print("For each square chain: t*=argmin, r=min(M0-t*,M1-t*), driver cuts u=t*+j, j in [1,r).")
print("shellRLCT(j)=1/2 * min_{k<=j} codim_k  (shell caps #small sing vals at j)")
print("ROUTE NEED (Lean carrierThreshold M) = 1/2 minAdm M ;  RECON target = (minAdm(u,M2)+ab)/2\n")
print(f"{'chain':>10} {'t*':>3} {'r':>2} {'j':>2} {'u':>2} {'ab':>3} {'codim_j':>7} {'shellRLCT':>9} {'routeNeed':>9} {'reconTgt':>8} {'>=need?':>7} {'>=recon?':>8}")
for (M0,M1,M2) in [(3,3,3),(4,4,4),(6,6,6),(8,8,8),(5,5,5),(4,4,6),(6,6,4),(4,6,6)]:
    mA,ts,vals=minAdm3(M0,M1,M2)
    r=min(M0-ts,M1-ts)
    # k* = argmin over k of codim by rank-B=k  (== ts for square? rank B = k on deepest pt)
    for j in range(1,r):
        u=ts+j; a=M0-u; b=M1-u; ab=a*b
        # shell caps rank B (=#small sing) at j' where deepest reachable r_B <= j (for M1<=M2) 
        # general: r_B_max = M1 - (min(M1,M2)-j); allowed strata r_B <= r_B_max
        rbmax = M1 - (min(M1,M2)-j)
        allowed=[k for k in range(0,min(M0,M1)+1) if k<=rbmax]
        shell_codim=min(vals[k] for k in allowed)
        shellRLCT=F(shell_codim,2)
        routeNeed=F(mA,2)
        reconTgt=F(minAdm2(u,M2)+ab,2)
        okneed = shellRLCT>=routeNeed
        okrecon= shellRLCT>=reconTgt
        print(f"{str((M0,M1,M2)):>10} {ts:>3} {r:>2} {j:>2} {u:>2} {ab:>3} {shell_codim:>7} {str(shellRLCT):>9} {str(routeNeed):>9} {str(reconTgt):>8} {str(okneed):>7} {str(okrecon):>8}")
    print()

print("=== flagCharge_ge check: minAdm M <= ab + minAdm(redChain u M) [=uM2 leaf] ===")
for (M0,M1,M2) in [(6,6,6),(4,4,4),(3,3,3)]:
    mA,ts,_=minAdm3(M0,M1,M2); r=min(M0-ts,M1-ts)
    for j in range(0,r+1):
        u=ts+j; ab=(M0-u)*(M1-u); rhs=ab+minAdm2(u,M2)
        print(f"  {(M0,M1,M2)} u={u} j={j}: minAdm={mA} <= ab({ab})+uM2({minAdm2(u,M2)})={rhs} : {mA<=rhs}  (routeNeed 1/2minAdm={F(mA,2)} <= reconTgt {F(rhs,2)})")
