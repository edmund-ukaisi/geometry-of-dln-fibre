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
def floor_u(M,u):return minAdm((u,)+tuple(M[2:]))   # minAdm(redChain u M)

# Verify the proof chain for interior u:
#  minAdm(M) <= ab + floor(u)         [peel recursion at t1=u]
#            <= ab + u*rho_d          [proven lemma floor<=u*min(M2,deepTailMin(u,..))=u*rho_d]
#            <= ab + u*M2 <= b*M0 + u*M2 = uM2+bM0
print("verify chain: minAdm <= ab+floor(u) <= ab+u*rho <= uM2+bM0, interior u")
bad1=bad2=bad3=bad4=0; tot=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        r=rho(M); M0,M1,M2=M[0],M[1],M[2]
        for u in range(0,min(M0,M1)+1):
            a,b=M0-u,M1-u
            if a+b>r: continue   # interior
            tot+=1
            ma=minAdm(M); fu=floor_u(M,u)
            if ma > a*b+fu: bad1+=1
            if fu > u*r: bad2+=1
            if a*b+u*r > u*M2+b*M0: bad3+=1
            if ma > u*M2+b*M0: bad4+=1
print(f"  interior cells tot={tot}")
print(f"  step1 minAdm<=ab+floor(u) fails={bad1}")
print(f"  step2 floor(u)<=u*rho     fails={bad2}")
print(f"  step3 ab+u*rho<=uM2+bM0   fails={bad3}")
print(f"  final minAdm<=uM2+bM0     fails={bad4}")
