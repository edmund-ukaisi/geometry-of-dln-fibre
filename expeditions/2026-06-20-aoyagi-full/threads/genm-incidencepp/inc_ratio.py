"""
Q3 crux test: is  G(z) <= K * (||Qp||_F^2)^(-q)  pointwise in z, with K bounded
over Qp scale AND conditioning?   (delta=commonDivisor handled separately; here delta=1.)

G(z) = ∫_{A_cor} det(Qb Qb^T)^(-a/2) ∫_{P,B,C} (||P Qp+B Qb||^2 + ||C Qp(I-Pi_b)||^2)^(-q) dP dB dC dA_cor
A_cor over box [-1,1]^{b*M2}.  We report R(z)=G(z)/||Qp||_F^(-2q).
Vary: scale of Qp (||Qp|| small..large) and conditioning cond(Qp) (u>=2).
Optionally restrict A_cor to a near-incidence tube to expose the corner; report both.
MC is a GUIDE (singular integrand). Many samples; also give the analytic corner cross-check for u=1.
"""
import numpy as np
from numpy.linalg import svd, det
rng=np.random.default_rng(3)

def proj_row(Qb):
    # projection onto row space of Qb (b x M2) -> M2 x M2
    U,S,Vt=svd(Qb,full_matrices=False)
    r=np.sum(S>1e-12)
    V=Vt[:r].T
    return V@V.T

def G_of_z(Qp,u,a,b,M2,q,Nfront=4000,NA=6000, shell=None, eps=0.3):
    """MC estimate of G(z). shell: None=full box; 'j1'=exactly 1 small sv of hsQ (<eps)."""
    tot=0.0; cnt=0
    A=rng.uniform(-1,1,size=(NA,b,M2))
    for Ac in A:
        Qb=Ac
        hsQ=np.vstack([Qp,Qb])
        if shell is not None:
            sv=svd(hsQ,compute_uv=False)
            nsmall=int(np.sum(sv<eps))
            if shell=='j1' and nsmall!=1: continue
        G=Qb@Qb.T
        dG=np.linalg.det(G)
        if dG<=1e-14: continue
        detfac=dG**(-a/2.0)
        Pib=proj_row(Qb)
        Qtr=Qp@(np.eye(M2)-Pib)   # u x M2
        # front MC
        P=rng.uniform(-1,1,size=(Nfront,u,u))
        B=rng.uniform(-1,1,size=(Nfront,u,b))
        C=rng.uniform(-1,1,size=(Nfront,a,u))
        Etop=np.sum((np.einsum('nij,jk->nik',P,Qp)+np.einsum('nij,jk->nik',B,Qb))**2,axis=(1,2))
        Etr =np.sum((np.einsum('nij,jk->nik',C,Qtr))**2,axis=(1,2))
        front=(2.0**(u*u+u*b+a*u))*np.mean((Etop+Etr)**(-q))
        tot+=detfac*front; cnt+=1
    vol_A=(2.0**(b*M2))
    if cnt==0: return np.nan
    return vol_A*tot/NA   # average over sampled A_cor (cnt/NA is the shell fraction, folded in)

def test(M,u,q,scales,conds, shell=None, seed=1):
    M0,M1,M2=M; a=M0-u; b=M1-u
    r=np.random.default_rng(seed)
    print(f"--- M={M} u={u} a={a} b={b} M2={M2} q={q} shell={shell} ---")
    for cond in conds:
        for sc in scales:
            # build Qp u x M2 with singular values geometric between sc and sc/cond
            svQp=np.array([sc*cond**(-i/(u-1) if u>1 else 0) for i in range(u)]) if u>1 else np.array([sc])
            Zc=r.standard_normal((M2,M2)); Vr=svd(Zc)[0]
            Up=svd(r.standard_normal((u,u)))[0] if u>1 else np.array([[1.0]])
            Sig=np.zeros((u,M2))
            for i in range(u): Sig[i,i]=svQp[i]
            Qp=Up@Sig@Vr.T
            frob=np.sum(Qp**2)
            G=G_of_z(Qp,u,a,b,M2,q,shell=shell)
            R=G/(frob**(-q))
            print(f"   cond={cond:5.1f} scale={sc:5.2f} ||Qp||^2={frob:7.3f}  G={G:.4e}  R=G/frob^-q={R:.4e}")

# anchor (3,3,3)@u=2: a=b=1, T1=3.5, q in (0,3). pick q=1.5 (safely below).
test((3,3,3),2, 1.5, scales=[0.3,1.0,3.0], conds=[1.0,5.0,25.0], shell=None)
print()
test((3,3,3),2, 1.5, scales=[0.3,1.0,3.0], conds=[1.0,5.0,25.0], shell='j1')
print()
# bigger corank (4,4,4)@u=2: a=b=2, minAdm(2,4)=8 -> comparator thr q<4; minAdm(4,4,4)=12,T1=6,q=c'-2.
# pick q=2.0
test((4,4,4),2, 2.0, scales=[0.3,1.0,3.0], conds=[1.0,5.0,25.0], shell=None)
