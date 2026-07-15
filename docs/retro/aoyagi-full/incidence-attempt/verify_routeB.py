import sympy as sp
# ROUTE-B audit, exact rationals. L=0 chains M=(M0,M1,M2).
# Lean defs (origin/genm-sj5-brickdcont):
#   redChain u (M0,M1,M2) = (u, M2)  [Fin 2 leaf]  => minAdm(redChain) = u*M2
#   tailMinWidth M = inf_{i in Fin(L+2)} M(i.succ) = min(M1,M2,...,M_last)  [INCLUDES M1]
#   minAdm(M) = min_t [(M0-t)(M1-t) + minAdm(redChain t M)] = min_t[(M0-t)(M1-t) + t*M2]
#   hpiv : minAdm(redChain u M) <= u * tailMinWidth M   (gates C_hle<top, step-4 D-B)
#   carrierThreshold = minAdm/2 = T1
# Route-B step-4 codim = u*tailMinWidth ; chain ceiling c' < ab/2 + (u*tailMinWidth)/2.
def minAdm3(M0,M1,M2): return min((M0-t)*(M1-t)+t*M2 for t in range(min(M0,M1)+1))
def tailMinWidth(M0,M1,M2): return min(M1,M2)            # L=0, INCLUDES M1 (per Lean def)
def minAdm_red(u,M2): return u*M2                          # redChain=(u,M2) leaf

print("=== tailMinWidth INCLUDES M1 (Lean: inf over M(i.succ)) — brief's 'M1 excluded' is FALSE ===")
print(f"  tailMinWidth(2,2,3)=min(M1,M2)=min(2,3)={tailMinWidth(2,2,3)}  (NOT M2=3)")
print()
print("=== hpiv (L=0)  <=>  u*M2 <= u*min(M1,M2)  <=>  M2 <= M1 ===\n")
rows=[("(2,2,3)",2,2,3,1,1),("(3,3,3)",3,3,3,2,1),("(3,3,4)",3,3,4,2,1),("(3,3,7)",3,3,7,2,2)]
print(f"{'chain':9} {'u,j':5} {'a,b':5} {'T1':6} {'minAdm_red':10} {'u*tMW':6} {'hpiv?':6} {'ceiling':8} {'shortfall(T1-ceil)':18} {'M2>M1'}")
for name,M0,M1,M2,u,j in rows:
    a,b=M0-u,M1-u; T1=sp.Rational(minAdm3(M0,M1,M2),2)
    mred=minAdm_red(u,M2); tmw=tailMinWidth(M0,M1,M2); utmw=u*tmw
    hpiv = mred <= utmw
    ceiling = sp.Rational(a*b,2) + sp.Rational(utmw,2)
    short = T1 - ceiling
    print(f"{name:9} {str((u,j)):5} {str((a,b)):5} {str(T1):6} {mred:<10} {utmw:<6} {str(hpiv):6} {str(ceiling):8} {str(short):18} {M2>M1}")
print()
print("Peel identity check: minAdm(M) <= ab + minAdm(red) [tight at argmin]; hpiv would give <= ab + u*tMW.")
for name,M0,M1,M2,u,j in rows:
    a,b=M0-u,M1-u
    print(f"  {name}: minAdm={minAdm3(M0,M1,M2)}, ab+minAdm_red={a*b+minAdm_red(u,M2)}, ab+u*tMW={a*b+u*tailMinWidth(M0,M1,M2)}")
