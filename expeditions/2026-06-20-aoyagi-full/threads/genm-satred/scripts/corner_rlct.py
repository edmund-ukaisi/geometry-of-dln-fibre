"""(D) convergence verify: sublevel-volume RLCT of the HONEST corner freedSchurLoss objects at
tight cells. Target: RLCT = 1/2 minAdm(M) (reaches threshold). freedSchurLoss = frobSq(P Q~p) +
frobSq(C Q~p + Gamma Q_b), Q~p=Q_p+P^-1 B12 Q_b; Q_p/Q_b = pivot/corank rows of prod(tailChain) A'."""
import numpy as np
rng=np.random.default_rng(0)
def prod_layers(As):
    P=As[0]
    for A in As[1:]: P=np.einsum('nij,njk->nik',P,A)
    return P
def rand(n,r,c): return rng.uniform(-1,1,(n,r,c))
def corner_F(M,u,N):
    # M=(M0,M1,M2,M3); cut u; a=M0-u,b=M1-u; tailChain=(M1,M2,M3)
    M0,M1,M2,M3=M; a=M0-u; b=M1-u
    # deep layers A' for tailChain (M1,M2,M3): A0'(M1xM2), A1'(M2xM3)
    A0=rand(N,M1,M2); A1=rand(N,M2,M3)
    W=prod_layers([A0,A1])            # M1 x M3  = prod(tailChain)
    Qp=W[:,:u,:]; Qb=W[:,u:,:]        # pivot rows / corank rows (kappa = first u rows)
    P=rand(N,u,u); B12=rand(N,u,b); C=rand(N,a,u); Gam=rand(N,a,b)
    # Q~p = Qp + P^-1 B12 Qb  (need P invertible; discard singular by tiny jitter—measure 0)
    loss=np.zeros(N)
    # pivot energy frobSq(P Q~p): if u>0
    if u>0:
        Pinv=np.linalg.inv(P + 1e-12*np.eye(u))
        Qtp = Qp + np.einsum('nij,njk,nkl->nil',Pinv,B12,Qb) if b>0 else Qp
        PE = np.einsum('nij,njk->nik',P,Qtp)
        loss += (PE**2).sum((-1,-2))
    else:
        Qtp = np.zeros((N,0,M3))
    # corank energy frobSq(C Q~p + Gamma Qb): if a>0
    if a>0:
        CE = (np.einsum('nij,njk->nik',C,Qtp) if u>0 else np.zeros((N,a,M3)))
        if b>0: CE = CE + np.einsum('nij,njk->nik',Gam,Qb)
        loss += (CE**2).sum((-1,-2))
    return loss
def minAdmRec(M):
    M=list(M);L=len(M)
    if L==1:return 0
    if L==2:return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec([t]+M[2:]) for t in range(min(M[0],M[1])+1))
ts=np.array([1e-2,3e-3,1e-3,3e-4,1e-4,3e-5])
def slope(F):
    V=np.array([(F<t).mean() for t in ts]); return np.diff(np.log(np.clip(V,1e-12,None)))/np.diff(np.log(ts))
cases=[("(2,2,2,2) SAT u=2 [a=0,b=0,A>2Δ]",(2,2,2,2),2),
       ("(2,3,4,4) SAT u=2 [a=0,b=1,A>2Δ]",(2,3,4,4),2),
       ("(2,1,2,2) DEEP-CORANK u=0 [a=2,b=1,k=2]",(2,1,2,2),0),
       ("(2,2,3,3) DEEP-CORANK u=0 [a=2,b=2,k=2]",(2,2,3,3),0),
       ("(2,2,3,3) SAT u=2 [a=0,b=0,A>2Δ]",(2,2,3,3),2)]
for lab,M,u in cases:
    thr=minAdmRec(list(M))/2
    F=corner_F(M,u,4_000_000); sl=slope(F)
    print(f"{lab}: target ½minAdm={thr}  measured λ→{sl[-1]:.3f}  trend {np.array2string(sl,precision=2)}")
