"""
Decorrelated check of Codex's claim: pointwise-in-z bound FAILS.
Front integral F(Qp,Qb,q)=∫_{P,B,C}(||P Qp+B Qb||^2 + ||C Qp(I-Pi_b)||^2)^{-q}
at Qp=diag(1,delta) (2x3, rank-dropping), Qb=e3.  Predict F ~ delta^{5-2q}.
So for q>5/2, F blows up as delta->0 while ||Qp||^2 ~ 1  => pointwise ratio unbounded.
Compare vs q<5/2 (my earlier q=1.5 range) where F->0.
"""
import numpy as np
rng=np.random.default_rng(7)

def proj_row(Qb):
    U,S,Vt=np.linalg.svd(Qb,full_matrices=False)
    r=np.sum(S>1e-12); V=Vt[:r].T
    return V@V.T

def Ffront(Qp,Qb,u,a,b,M2,q,N=3_000_000):
    Pib=proj_row(Qb); Qtr=Qp@(np.eye(M2)-Pib)
    P=rng.uniform(-1,1,(N,u,u)); B=rng.uniform(-1,1,(N,u,b)); C=rng.uniform(-1,1,(N,a,u))
    Et=np.sum((np.einsum('nij,jk->nik',P,Qp)+np.einsum('nij,jk->nik',B,Qb))**2,axis=(1,2))
    Er=np.sum((np.einsum('nij,jk->nik',C,Qtr))**2,axis=(1,2))
    return (2.0**(u*u+u*b+a*u))*np.mean((Et+Er)**(-q))

M2=3; u=2; a=1; b=1
Qb=np.zeros((1,3)); Qb[0,2]=1.0   # e3
print("M=(3,3,3) u=2 a=b=1; Qp=diag(1,delta) padded 2x3; Qb=e3")
print("predict F ~ delta^{5-2q}: grows for q>2.5, ->0 for q<2.5")
for q in [1.5, 2.8]:
    print(f"  q={q}  (5-2q={5-2*q:+.2f}):")
    prev=None
    for delta in [0.4,0.2,0.1,0.05]:
        Qp=np.zeros((2,3)); Qp[0,0]=1.0; Qp[1,1]=delta
        F=Ffront(Qp,Qb,u,a,b,M2,q)
        frob=1+delta**2
        ratio=F/(frob**(-q))
        slope="" if prev is None else f" slope={np.log(F/prev[1])/np.log(delta/prev[0]):+.2f}"
        print(f"    delta={delta:.3f}: F={F:.4e}  ratio F/||Qp||^-2q={ratio:.4e}{slope}")
        prev=(delta,F)
