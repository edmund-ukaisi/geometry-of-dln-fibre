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

# deep stratum {z0 Z Pi = 0}: codim = u*d, d=rho_d-b ; pole=2q-ub ; cond 2q-ub<u*d <=> 2q<u*rho_d
#   <=> 2c'-ab < u*rho_d - ub + ub... let me: 2q-ub<u(rho-b) <=> 2q<u*rho <=> 2c'-ab<u*rho <=> 2c'<u*rho+ab.
# candidate RHS_A = u*rho_d + ab  ; candidate RHS_B (corankrec QIP) = u*rho_d + b*M0
print("Check both candidate deep-condition RHS over interior cells (per u): minAdm <= RHS ?")
for label,rhsfun in [("A: u*rho+ab", lambda M0,M1,M2,u,a,b,r: u*r+a*b),
                     ("B: u*rho+b*M0", lambda M0,M1,M2,u,a,b,r: u*r+b*M0)]:
    failsA=0; tot=0; minmarg=999
    for arity in (3,4,5):
        for M in itertools.product(range(2,8),repeat=arity):
            r=rho(M)
            for u in interior_us(M):
                M0,M1,M2=M[0],M[1],M[2]; a,b=M0-u,M1-u
                tot+=1; ma=minAdm(M); rr=rhsfun(M0,M1,M2,u,a,b,r)
                if ma>rr: failsA+=1
                minmarg=min(minmarg, rr-ma)
    print(f"  RHS {label}: fails={failsA}/{tot}  min margin={minmarg}")

# also: is uses of the WRONG uM2 (my earlier): minAdm<=u*M2+b*M0 held; but urho+ab is TIGHTER (rho<=M2).
# print a few cells where rho<M2 to see the numbers
print("\ncells with rho<M2 (where uM2 vs urho differ):")
for M in [(4,4,5,3),(3,5,6,2),(5,5,6,3,3)]:
    r=rho(M)
    if r>=M[2]: continue
    for u in interior_us(M):
        M0,M1,M2=M[0],M[1],M[2];a,b=M0-u,M1-u
        print(f"  M={M} u={u}: minAdm={minAdm(M)} | uM2+bM0={u*M2+b*M0} urho+ab={u*r+a*b} urho+bM0={u*r+b*M0}")
