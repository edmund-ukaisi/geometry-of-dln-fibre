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
def rho(M):return min(M[2:])
def interior_us(M):
    r=rho(M);return [u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]
def phi_min_plus_ab(M,u):
    M0,M1=M[0],M[1];a,b=M0-u,M1-u;r=rho(M);d=r-b;md=min(u,d)
    rho0=(u+a)*md+u*b
    return a*b+min([rho0]+[rho0-l*(u+a)+l*(abs(u-d)+l) for l in range(1,md+1)])
# peel-at-(u-l) family bound: B_l = (a+l)(b+l) + (u-l)*rho_d  [peel t=u-l, redChain<=(u-l)rho_d]
def Bmin(M,u):
    M0,M1=M[0],M[1];a,b=M0-u,M1-u;r=rho(M)
    return min((a+l)*(b+l)+(u-l)*r for l in range(0,u+1))
print("Route: minAdm <= min_l B_l (peel t=u-l),  B_l=(a+l)(b+l)+(u-l)rho_d ; and B certifies ab+min_l phi ?")
f1=f2=tot=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            tot+=1
            if minAdm(M) > Bmin(M,u): f1+=1
            if Bmin(M,u) > phi_min_plus_ab(M,u): f2+=1
print(f"  cells={tot}  minAdm>min_l B_l fails={f1}   min_l B_l > ab+min_l phi fails={f2}")
print("  (f1=0: peel-at-(u-l) family proves minAdm<=min_l B_l; f2=0: B_l certifies the RLCT condition ab+min_l phi)")
