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
def infpivot(M):   # corankrec's landed full-min corollary
    M0,M1=M[0],M[1];r=rho(M)
    return min((M0-up)*(M1-up)+up*r for up in range(0,min(M0,M1)+1))

# CORRECTED condition: 2q < ub + Lambda, Lambda=minAdm((u+a,u,d)), d=rho_d-b => minAdm M <= ab+ub+Lambda
# Also Codex Lambda = min_{0<=r<=min(u,d)}{ud + r^2 + (a-d)r}; verify Lambda==minAdm((u+a,u,d))
def Lam_codex(u,a,d):
    m=min(u,d); return min(u*d + r*r + (a-d)*r for r in range(0,m+1)) if d>=0 else 0
print("(x) Codex Lambda == minAdm((u+a,u,d)) ?")
mm=0
for u in range(1,7):
    for a in range(1,7):
        for d in range(1,8):
            if Lam_codex(u,a,d)!=minAdm((u+a,u,d)): mm+=1
print(f"   mismatch={mm}")

print("\n(A) forall-cell CORRECTED: minAdm M <= ab+ub+minAdm((u+a,u,d)), d=rho_d-b")
f=0;tot=0;mn=999
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u;d=rho(M)-b
            tot+=1; ma=minAdm(M); rhs=a*b+u*b+minAdm((u+a,u,d))
            if ma>rhs: f+=1
            mn=min(mn,rhs-ma)
print(f"   cells={tot} FAILS={f} min-margin={mn}")

print("\n(B) full-min corollary certifies it: infpivot(M) <= ab+ub+minAdm((u+a,u,d)) for all interior u ?")
f2=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        ip=infpivot(M)
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u;d=rho(M)-b
            if ip > a*b+u*b+minAdm((u+a,u,d)): f2+=1
print(f"   infpivot > ab+ub+Lambda fails={f2}  (0 => corankrec's minAdm_le_inf_pivot_qip certifies the corrected condition)")
