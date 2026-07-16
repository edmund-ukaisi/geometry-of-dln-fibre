import itertools, math
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

# Codex true condition: 2q < min_{l=0..min(u,d)} phi(l), phi(l)=rho0 + l^2 + (d-2u-a) l
#   rho0 = (u+a)*min(u,d) + u*b ; d = rho_d - b ; k_l=l(u+a), c_l=l(d-u+l) [valid d>=u; for d<u strata capped]
# need minAdm <= ab + min_l phi(l)  (so c'<minAdm/2 => 2c'<ab+min_l phi => 2q<min_l phi)
def true_RHS(M,u):
    M0,M1,M2=M[0],M[1],M[2]; a,b=M0-u,M1-u; r=rho(M); d=r-b
    mind=min(u,d)
    rho0=(u+a)*mind + u*b
    # phi(l) for l=0..mind ; but c_l=l(d-u+l) only valid when the rank-(u-l) locus is codim l(d-u+l); for d<u handle by mind
    best=None
    for l in range(0, mind+1):
        cl=l*(d-u+l) if d>=u else l*(mind-(mind-l))  # for d<u, rank(QPi)<=d already; use generic determinantal on u x d: {rank<=d-l'}
        # For d<u: QPi is u x d rank d generically; corank-l' means rank d-l', codim l'(u-d+l') in the u x d matrix; l' from 1..d
        # unify: let w=min(u,d)=mind (generic rank); dropping to rank w-l has codim l*(|u-d|+l). k_l=l(u+a).
        cl = l*(abs(u-d)+l)
        phi = rho0 - l*(u+a) + cl
        best = phi if best is None or phi<best else best
    ab=a*b
    return ab+best, rho0, d

print("TRUE interior condition (Codex strata): minAdm <= ab + min_l phi(l) ?")
fails=0; tot=0; minmarg=999; failex=[]
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            tot+=1; ma=minAdm(M); rhs,rho0,d=true_RHS(M,u)
            if ma>rhs:
                fails+=1
                if len(failex)<20: failex.append((M,u,ma,rhs,d))
            minmarg=min(minmarg,rhs-ma)
print(f"  interior cells={tot}  FAILS (minAdm>ab+min_l phi)={fails}  min margin={minmarg}")
for e in failex: print("   FAIL",e)

# also report: for how many cells is the intermediate stratum STRICTLY tighter than form A (urho+ab)?
tighter=0
for arity in (3,4):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u;r=rho(M)
            rhs,_,d=true_RHS(M,u)
            formA=a*b+u*r
            if rhs<formA: tighter+=1
print(f"\n  cells where intermediate stratum < form A (urho+ab): {tighter}")
