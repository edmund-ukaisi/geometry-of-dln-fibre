import numpy as np
# LOCAL codim + LOCAL rlct at x0 = aligned diag (1,0)/(1,0)/(0,1) for chain (2,2,2,2).
B0=np.array([[1.,0],[0,0]]); B1=np.array([[1.,0],[0,0]]); B2=np.array([[0.,0],[0,1]])
def Zof(v):
    L0=B0+v[0].reshape(2,2); L1=B1+v[1].reshape(2,2); L2=B2+v[2].reshape(2,2)
    return L2@L1@L0
def loss(vs): return np.array([ (Zof(v)**2).sum() for v in vs])
def dmu_rank_at(d0,d1,d2,eps=1e-6):
    L0=B0+d0;L1=B1+d1;L2=B2+d2; base=(L2@L1@L0).ravel(); cols=[]
    for k,M in enumerate((L0,L1,L2)):
        for idx in np.ndindex(2,2):
            dM=np.zeros((2,2)); dM[idx]=eps
            Ls=[L0,L1,L2]; Ls=[x.copy() for x in Ls]; Ls[k]=Ls[k]+dM
            cols.append(((Ls[2]@Ls[1]@Ls[0]).ravel()-base)/eps)
    return np.linalg.matrix_rank(np.array(cols).T,tol=1e-4)
# local codim = max rank dmu over NEARBY fiber points (small perturbations staying on Z=0)
rng=np.random.default_rng(0); best=0; cnt=0
for _ in range(20000):
    # random small perturbation, then project to fiber by a couple of Newton-ish steps is hard;
    # instead: build nearby fiber pts by small rank-preserving moves that keep Z=0.
    # Move: L0->L0+s*(col in span e1), L1->L1 with row structure, L2->L2 small in ker-preserving way.
    s=0.3
    d0=np.zeros((2,2)); d1=np.zeros((2,2)); d2=rng.normal(size=(2,2))*s   # L2 free (Z=L2L1L0, L1L0=diag(1,0)*? )
    L0=B0+d0; L1=B1+d1
    P=L1@L0  # = diag(1,0)
    # to keep Z=0 need (B2+d2) P =0 -> d2 P = -B2 P; B2 P = diag(0,1)diag(1,0)=0, so need d2 P=0 -> d2 col1=0
    d2[:,0]=0
    # also perturb L0,L1 keeping (B2+d2)(B1+d1)(B0+d0)=0 to first order... just test rank at this fiber pt
    L2=B2+d2
    if np.linalg.norm(L2@L1@L0)>1e-9: continue
    cnt+=1; best=max(best,dmu_rank_at(d0,d1,d2))
print(f"aligned-diag: rank dmu at x0 = {dmu_rank_at(np.zeros((2,2)),np.zeros((2,2)),np.zeros((2,2)))}, "
      f"max nearby rank(=local codim lower est) = {best} over {cnt} nearby fiber pts")

# LOCAL rlct via tube on small perturbations (scale-limited local germ)
def local_tube(scale, N=4_000_000, seed=1):
    rng=np.random.default_rng(seed)
    vs=[rng.uniform(-scale,scale,size=(N,3,4))][0]
    f=loss(vs)
    ts=np.array([1e-4,3e-5,1e-5,3e-6,1e-6])*scale**2   # tube thresholds scaled
    P=np.array([(f<=t).mean() for t in ts]); m=P>0
    lam=np.polyfit(np.log(ts[m]),np.log(P[m]),1)[0] if m.sum()>=2 else float('nan')
    sl=np.diff(np.log(P[m]))/np.diff(np.log(ts[m])) if m.sum()>=2 else []
    return lam, sl, P
lam,sl,P=local_tube(0.15)
print(f"local rlct estimate at aligned-diag (scale 0.15): fit={lam:.3f}  slopes={np.round(sl,2)}  P={['%.1e'%x for x in P]}")
