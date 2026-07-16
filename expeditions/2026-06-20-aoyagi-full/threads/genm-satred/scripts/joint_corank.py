"""(D) CRUX: does the JOINT (Gamma, A_cor) integration recover the full corank charge ab/2 at k>=2,
where the SEQUENTIAL {Gamma=0}-polar-then-angular-J route undershoots?
Object: Ch_joint(c') = int_{Gamma(a x b), A_cor(b x M2)} frobSq(Gamma . A_cor . S)^{-c'}, S fixed generic
rank rho (M2 x q). RLCT should = ab/2 if the joint resolution recovers the full charge; < ab/2 = undershoot.
(worst case C=0; C generic only helps.) Measure RLCT via sublevel-volume slope."""
import numpy as np
rng=np.random.default_rng(1)
def make_S(M2,q,rho):
    # fixed generic rank-rho M2 x q matrix
    U=rng.standard_normal((M2,rho)); V=rng.standard_normal((rho,q)); return U@V
def Ch_joint_F(a,b,M2,q,rho,N):
    S=make_S(M2,q,rho)
    Gam=rng.uniform(-1,1,(N,a,b)); Ac=rng.uniform(-1,1,(N,b,M2))
    K=np.einsum('nij,jk->nik',Ac,S)          # A_cor . S : b x q
    P=np.einsum('nij,njk->nik',Gam,K)         # Gamma . (A_cor S): a x q
    return (P**2).sum((-1,-2))
ts=np.array([1e-2,3e-3,1e-3,3e-4,1e-4,3e-5,1e-5])
def slope(F):
    V=np.array([(F<t).mean() for t in ts]); return np.diff(np.log(np.clip(V,1e-12,None)))/np.diff(np.log(ts))
print("Joint corank charge RLCT vs ab/2 (k=a+b-rho):")
for (a,b,M2,q,rho) in [(2,1,2,2,1),   # k=2: (2,1,2,2)@t=0 style, ab/2=1
                       (2,2,3,3,2),   # k=2: (2,2,3,3)@t=0 style, ab/2=2
                       (3,1,3,4,2),   # k=2: (4,2,3,4)@t=1 style (a=3,b=1,rho=2), ab/2=1.5
                       (2,2,4,4,2),   # k=2, ab/2=2
                       (1,1,2,2,1),   # k=1 edge check, ab/2=0.5
                       (3,2,3,3,2)]:  # k=3, ab/2=3
    k=a+b-rho
    F=Ch_joint_F(a,b,M2,q,rho,4_000_000); sl=slope(F)
    print(f"  a={a} b={b} rho={rho} (k={k}): ab/2={a*b/2}  measured RLCT→{sl[-1]:.3f}  trend {np.array2string(sl,precision=2)}")
