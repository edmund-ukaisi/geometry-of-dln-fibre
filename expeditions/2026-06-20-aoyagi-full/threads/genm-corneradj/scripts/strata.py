# Check the per-stratum reduction bookkeeping for the DEEP corank (a,b>=1, k=a+b-rho>=2).
# On stratum rank(K)=rank(A_cor Zf)=r (0<=r<=b), effective b x rho A_cor (Zf rank rho):
#   Gamma-image dim = a*r  -> Gamma-reduction = a*r/2
#   A_cor codim to {rank<=r} in b x rho = (b-r)(rho-r)
# HYPOTHESIS A (single chain redChain u M, reduction_r = Gamma + A_cor-transverse):
#   red_r = a*r/2 + (rho-b) ... ? test vs the top stratum ab/2 and the binding requirement.
# Cleaner: total charge on stratum r that must combine with the reduced structure.
# Test the identity: does min over r of [a*r + (b-r)(rho-r)] relate to ab? and the k-dependence.
def report(a,b,rho):
    k=a+b-rho
    print(f"\n a={a} b={b} rho={rho}  k=a+b-rho={k}  (ab={a*b})")
    print(f"   {'r':>2} {'Gamma-red 2x=a*r':>16} {'Acor-codim (b-r)(rho-r)':>24} {'top-only red_r=a*r/2':>20}")
    for r in range(0,b+1):
        gr=a*r; cod=(b-r)*(rho-r)
        # 'top-only' single-chain naive reduction if we DON'T give deeper strata a bigger chain:
        # reduction contributed = a*r/2 (Gamma on image) + cod/2 (Acor transverse pays)
        red_single = a*r/2 + cod/2
        print(f"   {r:>2} {gr:>16} {cod:>24} {'':>4}a*r/2+cod/2 = {red_single}")
    # the r=b-1 stratum single-chain reduction:
    r=b-1
    if r>=0:
        red=a*r/2 + (b-r)*(rho-r)/2
        print(f"   -> r=b-1 single-chain reduction = {red}  (top ab/2={a*b/2}); deficit={a*b/2-red}=(k-1)/2? {(k-1)/2}")
for (a,b,rho) in [(2,2,3),(2,2,2),(3,1,2),(2,3,4),(2,2,4),(3,3,3),(1,2,2)]:
    report(a,b,rho)
