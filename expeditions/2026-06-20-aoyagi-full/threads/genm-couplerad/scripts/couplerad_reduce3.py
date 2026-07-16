import itertools
def mval(M,T):
    L=len(M)-1;v=0
    for j in range(L):
        tp=M[0] if j==0 else T[j-1];v+=(tp-T[j])*(M[j+1]-T[j])
    return v
def minAdm(M):
    L=len(M)-1
    if L==0:return 0
    bnd=[min(M[0],M[1])]+[M[j+1] for j in range(1,L)]
    best=None
    for T in itertools.product(*[range(bnd[j]+1) for j in range(L)]):
        if T[-1]!=0:continue
        if any(T[i]<T[i+1] for i in range(L-1)):continue
        v=mval(M,T);best=v if best is None or v<best else best
    return best
def min_phi(u,a,b,d):
    md=min(u,d); rho0=(u+a)*md+u*b
    return min([rho0]+[rho0-l*(u+a)+l*(abs(u-d)+l) for l in range(1,md+1)])

print("Test: min_l phi(l) == u*b + minAdm((u+a, u, d)) ?   [d = rho_d - b]")
print("  (transverse-stratum criterion = free-Gaussian ub-block + arity-3 RLCT of reduced (E,Y) chain)")
fails=0; tot=0; ex=[]
for u in range(1,7):
    for a in range(1,7):
        for b in range(0,7):
            for d in range(0,8):
                mp=min_phi(u,a,b,d)
                arity3 = u*b + minAdm((u+a,u,d)) if d>=1 else u*b + 0
                tot+=1
                if mp!=arity3:
                    fails+=1
                    if len(ex)<12: ex.append((u,a,b,d,mp,arity3))
print(f"  total={tot}  MISMATCH={fails}")
for e in ex: print("   MISMATCH (u,a,b,d,min_phi,ub+minAdm(u+a,u,d)):",e)
# also try the reversed chain (d,u,u+a) in case of convention
fails2=0
for u in range(1,7):
    for a in range(1,7):
        for b in range(0,7):
            for d in range(1,8):
                if min_phi(u,a,b,d)!= u*b+minAdm((d,u,u+a)): fails2+=1
print(f"  reversed chain (d,u,u+a): MISMATCH={fails2}")
