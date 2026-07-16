import numpy as np, itertools
# (1) CONFIRM the log divergence at 2q=ub: int_{box}(c+||B~Qb||^2)^{-ub/2}dB~ ~ A*log(1/c)+B (GROWS, not bounded)
def Bint(c,q,u,b,Qb,N=400000,seed=0):
    rng=np.random.default_rng(seed); G=Qb@Qb.T
    B=rng.uniform(-1,1,(N,u,b)); val=np.einsum('nij,jk,nik->ni',B,G,B).sum(axis=1)
    return ((c+val)**(-q)).mean()*2.0**(u*b)
print("(1) 2q=ub boundary: does int GROW like log(1/c)?  (u=2,b=1,ub=2,q=1 => 2q=2=ub)")
np.random.seed(1); Qb=np.random.randn(1,2)
cs=[10**-k for k in range(1,7)]
vals=[Bint(c,1.0,2,1,Qb) for c in cs]
for c,v in zip(cs,vals): print(f"   c={c:.0e}  int={v:.3f}   log(1/c)={np.log(1/c):.3f}")
# fit int = A*log(1/c)+B
A,B=np.polyfit([np.log(1/c) for c in cs], vals,1)
print(f"   fit int ≈ {A:.3f}*log(1/c) + {B:.3f}  => {'LOG-DIVERGENT (A>0, grows)' if A>0.1 else 'bounded'}  [corankrec: log, NOT bounded]")

# (2) Is the boundary 2q=ub REACHABLE in a cell's c'-window? boundary in (ab/2,½minAdm M) iff minAdm M > ab+ub
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
print("\n(2) boundary 2q=ub reachable iff minAdm M > ab+ub. Count interior cells with minAdm M > ab+ub:")
reach=0; tot=0; ex=[]
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u; tot+=1
            if minAdm(M) > a*b+u*b:
                reach+=1
                if len(ex)<10: ex.append((M,u,minAdm(M),a*b+u*b))
print(f"   interior cells={tot}  boundary-reachable (minAdm>ab+ub)={reach}")
for e in ex: print(f"     M={e[0]} u={e[1]}: minAdm={e[2]} > ab+ub={e[3]}")

# (3) At boundary-reachable cells, is minAdm((u+a,u,d))>=1 (so log<=eps -> RectSchurCore(eps) works)?
print("\n(3) at boundary-reachable cells: minAdm((u+a,u,d)) >= 1 ?  (d=rho_d-b)")
bad=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u;d=rho(M)-b
            if minAdm(M) > a*b+u*b:
                if minAdm((u+a,u,d)) < 1: bad+=1
print(f"   boundary-reachable cells with minAdm((u+a,u,d))<1 (log/eps step FAILS): {bad}")
