"""
(a) Sanity: Codex's joint incidence exponents  C_{l,s}=ub+M0*l+(M0-s)(u-l-s)+s*(d-l), d=M2-b,
    over reachable (l,s). min_{l,s} C_{l,s}/2 should be >= T1_q = T1-ab/2 (so LHS finite for q<T1).
    Compare min to shellj's lambda_j and to comparator threshold uM2/2.
(b) Full INTEGRATED corner (2,2,3)@u=1: LHS_int(q)=∫_{z0,Acor,P,B,C} det^-1/2 (Etop+Etr)^-q
    vs comparator(q)=∫_{z0 in box}||z0||^-2q.  ratio bounded for q<3/2=T1_q ? K~1/(3/2-q)?
"""
import numpy as np
from itertools import product
rng=np.random.default_rng(11)

# ---------- (a) exponent arithmetic ----------
def minAdm3(M0,M1,M2):
    return min((M0-s)*(M1-s)+s*M2 for s in range(0,min(M0,M1)+1))
def Cls(M0,u,d,l,s):
    return u*(u+ (0)) *0 + 0  # placeholder; use explicit below

def check_case(M,u):
    M0,M1,M2=M; a=M0-u; b=M1-u; d=M2-b
    T1=minAdm3(M0,M1,M2)/2; T1q=T1-a*b/2; comp=u*M2/2.0
    best=None
    # l = dim(row Qp ∩ row Qb) i.e. rank drop of W=Qp(I-Pi_b); ranges 0..min(u,?); s=rank Y2 0..
    for l in range(0,u+1):
        for s in range(0, M0+1):
            # feasibility: need u-l-s>=0 and d-l>=0 (chart sizes nonneg)
            if u-l-s<0 or d-l<0: continue
            C = u*b + M0*l + (M0-s)*(u-l-s) + s*(d-l)
            if best is None or C<best[0]:
                best=(C,l,s)
    Cmin,l,s=best
    print(f"  M={M} u={u} a={a} b={b} d=M2-b={d}: T1={T1} T1q(=T1-ab/2)={T1q}  comparator uM2/2={comp}")
    print(f"     min C_ls/2={Cmin/2}  at (l={l},s={s})   [need min C/2 >= T1q for LHS finite to T1]  {'OK' if Cmin/2>=T1q-1e-9 else 'BELOW T1q!'}")

print("=== (a) Codex joint-incidence exponents vs T1q ===")
for M,u in [((2,2,3),1),((3,3,3),2),((3,3,5),2),((4,4,4),2),((6,6,6),4),((6,6,6),5),((3,3,6),2)]:
    check_case(M,u)

# ---------- (b) full integrated corner (2,2,3)@u=1 ----------
def Ffront_corner(z0,Qb,q,N=200000):
    # z0:1x3 (=Qp), Qb:1x3.  P,B,C scalars.
    M2=3
    U,S,Vt=np.linalg.svd(Qb.reshape(1,3),full_matrices=False); r=np.sum(S>1e-12); V=Vt[:r].T
    Pib=V@V.T
    Qtr=(z0.reshape(1,3))@(np.eye(3)-Pib)
    p=rng.uniform(-1,1,N); be=rng.uniform(-1,1,N); ga=rng.uniform(-1,1,N)
    Et=np.sum((np.outer(p,z0)+np.outer(be,Qb))**2,axis=1)
    Er=(ga**2)*np.sum(Qtr**2)
    return 8.0*np.mean((Et+Er)**(-q))

def LHS_int(q, Nz=4000, NA=4000):
    tot=0.0
    for _ in range(Nz):
        z0=rng.uniform(-1,1,3)
        # sample A_cor; importance near incidence (Qb ~ z0 direction) and near 0 handled by det
        acc=0.0; cnt=0
        for _ in range(NA//Nz if NA>=Nz else 1):
            Qb=rng.uniform(-1,1,3)
            dG=np.sum(Qb**2)
            if dG<1e-10: continue
            acc+= dG**(-0.5) * Ffront_corner(z0,Qb,q,N=2000)
            cnt+=1
        if cnt>0: tot+= (8.0)*acc/cnt   # A_cor box vol 8
    return (8.0)*tot/Nz   # z0 box vol 8

def comparator(q, Nz=2_000_000):
    z0=rng.uniform(-1,1,(Nz,3))
    n2=np.sum(z0**2,axis=1)
    return 8.0*np.mean(n2**(-q))

print("\n=== (b) integrated corner (2,2,3)@u=1: ratio LHS_int/comparator, T1q=3/2 ===")
for cprime in [0.9,1.1,1.3,1.4]:
    q=cprime-0.5
    L=LHS_int(q); Cc=comparator(q)
    print(f"  c'={cprime} q={q:.2f}: LHS_int={L:.4e} comparator={Cc:.4e} ratio K={L/Cc:.4e}  K*(1.5-q)={L/Cc*(1.5-q):.4e}")
