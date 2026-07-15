import numpy as np
from rlct_tools import minAdm
# 3-layer (2,2,2,2): find fiber points x0 (Z=0) with rank(Hess K) < minAdm=3 (=> higher-order residual,
# candidate deficit). Hess K at a zero = 2 (dZ)^T (dZ); rank = rank of the differential dmu.
rng=np.random.default_rng(0)
def Zof(L0,L1,L2): return L2@L1@L0
def dmu_rank(L0,L1,L2,eps=1e-6):
    base=Zof(L0,L1,L2).ravel(); cols=[]
    for M in (L0,L1,L2):
        for idx in np.ndindex(M.shape):
            M2=M.copy(); M2[idx]+=eps
            Ls=[L0.copy(),L1.copy(),L2.copy()]; Ls[[id(L0),id(L1),id(L2)].index(id(M))]=M2
            cols.append((Zof(*Ls).ravel()-base)/eps)
    return np.linalg.matrix_rank(np.array(cols).T,tol=1e-4)
ma=minAdm((2,2,2,2)); print("minAdm(2,2,2,2)=",ma)
found={}
def rank_profiles(L0,L1,L2):
    r=lambda M:np.linalg.matrix_rank(M,tol=1e-6)
    return (r(L0),r(L1),r(L2),r(L1@L0),r(L2@L1),r(L2@L1@L0))
for _ in range(60000):
    # construct fiber points by forcing Z=0 via various rank-drop mechanisms
    m=rng.integers(0,6)
    L0=rng.normal(size=(2,2));L1=rng.normal(size=(2,2));L2=rng.normal(size=(2,2))
    if m==0: L1=np.zeros((2,2))
    if m==1: L0=np.outer(rng.normal(2),rng.normal(2))*0+np.outer(rng.normal(size=2),rng.normal(size=2)); # L0 rank1
    if m==2: # L1L0=0: L0 rank1 col-space = ker L1
        u=rng.normal(size=2); L0=np.outer(rng.normal(size=2),u)  # col space span(rand), make L1 kill it
        w=rng.normal(size=2); L1=np.outer(w, np.array([u[1],-u[0]]))  # row orth to L0 col? ensure L1 L0=0
    if m==3: # L2(L1L0)=0 with L1L0 rank1
        L0=np.outer(rng.normal(size=2),rng.normal(size=2)); P=L1@L0
        if np.linalg.matrix_rank(P,tol=1e-9)>=1:
            U,s,Vt=np.linalg.svd(P); c=U[:,0]  # col space of P
            L2=np.outer(rng.normal(size=2), np.array([c[1],-c[0]]))  # rows orth to c => L2 c=0
    if m==4: L2=np.zeros((2,2))
    if m==5: L0=np.zeros((2,2))
    if np.linalg.norm(Zof(L0,L1,L2))>1e-9: continue
    r=dmu_rank(L0,L1,L2)
    prof=rank_profiles(L0,L1,L2)
    key=(r,prof)
    found[key]=found.get(key,0)+1
print("(rank dmu = rank Hess K , rank-profile(L0,L1,L2,L1L0,L2L1,Z)) : count")
for k in sorted(found): 
    tag="  <-- Hess-rank < minAdm (higher-order residual)" if k[0]<ma else ""
    print("  ",k, found[k], tag)
