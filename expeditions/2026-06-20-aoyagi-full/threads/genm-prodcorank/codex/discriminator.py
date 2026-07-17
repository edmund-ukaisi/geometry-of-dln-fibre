from functools import lru_cache
from fractions import Fraction as F

def redChain(t,M): return (t,)+M[2:]
@lru_cache(None)
def minAdm(M):
    L=len(M)
    if L==1: return 0
    if L==2: return M[0]*M[1]
    best=None
    for t in range(0,min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdm(redChain(t,M))
        best=v if best is None else min(best,v)
    return best
def Ck(k): return k*k-(k*k)//4

print("=== outer-peel stratification of (n,n,n,n): naive m^2 vs product C_m, per deeper corank m ===")
print("stratum m = deeper corank; reduced = (n-m, n, n); c* = minAdm(n,n,n,n)/2")
for n in range(3,9):
    cstar=F(minAdm((n,n,n,n)),2)
    print(f"\n n={n}: minAdm={minAdm((n,n,n,n))}, c*={cstar}")
    naive_ok=True; prod_min=None; naive_min=None
    for m in range(0,n+1):
        red=(n-m,n,n)
        Tred=F(minAdm(red),2)
        Tnaive=F(m*m,2)+Tred
        Tprod=F(Ck(m),2)+Tred
        naive_min = Tnaive if naive_min is None else min(naive_min,Tnaive)
        prod_min  = Tprod  if prod_min  is None else min(prod_min, Tprod)
        flagN = "OK" if Tnaive>=cstar else "UNDERSHOOT"
        flagP = "OK" if Tprod>=cstar else "UNDERSHOOT"
        print(f"   m={m}: minAdm(red={red})={minAdm(red)} | naive m^2={m*m} -> T={Tnaive} [{flagN}] | prod C_m={Ck(m)} -> T={Tprod} [{flagP}]")
    print(f"   => min over strata: naive={naive_min} (==c*? {naive_min==cstar}); product={prod_min} (<c*? {prod_min<cstar})")
