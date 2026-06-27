import itertools
def Mval(M, T):
    # M: tuple length L+1 ; T: tuple length L (Aoyagi exponents t^(1)..t^(L))
    L=len(T)
    s=0
    for j in range(L):
        tprev = M[0] if j==0 else T[j-1]
        s += (tprev - T[j])*(M[j+1] - T[j])
    return s
def admBound(M,j,L):
    return min(M[0],M[1]) if j==0 else M[j+1]
def adm_paths(M):
    L=len(M)-1
    bounds=[admBound(M,j,L) for j in range(L)]
    res=[]
    for T in itertools.product(*[range(b+1) for b in bounds]):
        # weak decrease t^1>=...>=t^L, last=0
        if any(T[j] > T[i] for i in range(L) for j in range(L) if i<=j and not T[j]<=T[i]): pass
        ok = all(T[j]<=T[i] for i in range(L) for j in range(L) if i<=j)
        if not ok: continue
        if T[L-1]!=0: continue
        res.append(T)
    return res

for M in [(4,4,2,2),(3,3,4),(2,2,1),(2,2,2)]:
    paths=adm_paths(M)
    vals=[(T,Mval(M,T)) for T in paths]
    minv=min(v for _,v in vals)
    minimizers=[T for T,v in vals if v==minv]
    print(f"M={M}: minAdm={minv}, #minimizers={len(minimizers)}")
    for T in minimizers:
        # per-term codims
        terms=[]
        for j in range(len(T)):
            tprev = M[0] if j==0 else T[j-1]
            terms.append((tprev-T[j])*(M[j+1]-T[j]))
        print(f"    T={T} (t^1..t^L), per-layer codims={terms}, sum={sum(terms)}")
