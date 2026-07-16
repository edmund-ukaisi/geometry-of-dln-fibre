# Structure decide-check for the ray-concavity proof route.
# D_M(x) = minAdm((x, M2, ..., Mlast)) = minAdm(redChain x M).  tail T=(M2,...,Mlast).
# Recursion: D_M(x) = min_{s<=min(x,M2)} [(x-s)(M2-s) + E(s)],  E(s)=minAdm((s,)+T') , T'=(M3,...,Mlast).
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def D(tail, x):                       # D_M(x) with tail=(M2,...,Mlast)
    return minAdm((x,)+tuple(tail))
def Dcells(tail, x):                  # list of (s, value) over the x-dependent domain s<=min(x,M2)
    M2=tail[0]; Tp=tail[1:]
    return [(s, (x-s)*(M2-s)+minAdm((s,)+tuple(Tp))) for s in range(min(x,M2)+1)]
def argmin_s(tail,x):
    cells=Dcells(tail,x); m=min(v for _,v in cells)
    return [s for s,v in cells if v==m]

# Enumerate tails (M2,...,Mlast), lengths 1..4 (=> arity M 3..6), widths 1..6.  x up to 8.
fullconcave_fail=[]; ray_fail=[]; domain_binding=[]; minmono_fail=[]
Ntails=0
for taillen in range(1,5):
    for tail in product(range(1,7),repeat=taillen):
        Ntails+=1
        M2=tail[0]; Tp=tail[1:]
        vals=[D(tail,x) for x in range(0,9)]
        # (a) full discrete concavity: 2 D(x) >= D(x-1)+D(x+1)
        for x in range(1,8):
            if not (2*vals[x] >= vals[x-1]+vals[x+1]):
                fullconcave_fail.append((tail,x,vals[x-1],vals[x],vals[x+1]))
        # (b) ray form u D(t) >= t D(u)
        for t in range(1,9):
            for u in range(t+1,9):
                if not (u*vals[t] >= t*vals[u]): ray_fail.append((tail,t,u,vals[t],vals[u]))
        # (c) is the x-domain constraint s<=x ever binding? i.e. does the UNCONSTRAINED
        #     envelope (s in [0,M2], line (M2-s)x + [E(s)-s(M2-s)]) beat D(x)?
        for x in range(0,9):
            Efull = min( (M2-s)*x + (minAdm((s,)+tuple(Tp)) - s*(M2-s)) for s in range(0,M2+1) )
            if Efull < vals[x]:      # unconstrained strictly smaller => constraint s<=x is BINDING
                domain_binding.append((tail,x,Efull,vals[x]))
        # (d) minimizer monotone non-decreasing in x? (use the SMALLEST argmin)
        prev=-1
        for x in range(0,9):
            s0=min(argmin_s(tail,x))
            if s0<prev: minmono_fail.append((tail,x,s0,prev))
            prev=s0
print(f"tails checked: {Ntails}")
print(f"(a) FULL concavity failures: {len(fullconcave_fail)}   {fullconcave_fail[:5]}")
print(f"(b) ray-form failures:       {len(ray_fail)}   {ray_fail[:5]}")
print(f"(c) x-domain constraint BINDING (unconstrained envelope beats D): {len(domain_binding)}   {domain_binding[:8]}")
print(f"(d) smallest-argmin NON-monotone in x: {len(minmono_fail)}   {minmono_fail[:8]}")
