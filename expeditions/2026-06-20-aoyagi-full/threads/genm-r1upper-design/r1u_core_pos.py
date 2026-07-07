import numpy as np
rng=np.random.default_rng(0)
# The atom needs core w = ‖A Q̃_p‖² + ‖C Q̃_p (I-P_{Q_b})‖² > 0.  ‖A Q̃_p‖²>0 iff Q̃_p≠0 (A invertible).
# Q̃_p = Q_p + A⁻¹B Q_b. When is Q̃_p = 0 (i.e. w could be 0)? Only on a NULL locus (poly eqn) generically.
# Check: over random chart configs, is w>0 essentially always, and is {Q̃_p=0} null?
def wcore(M0,M1,t,n,N=200000):
    p=M0-t; q=M1-t; zeros=0; wmin=1e9
    for _ in range(2000):
        A=rng.standard_normal((t,t))
        if abs(np.linalg.det(A))<1e-6: continue
        B=rng.standard_normal((t,q)); C=rng.standard_normal((p,t))
        Q=rng.standard_normal((M1,n)); Qp=Q[:t]; Qb=Q[t:]
        if np.linalg.matrix_rank(Qb)<q: continue
        Qtp=Qp+np.linalg.inv(A)@B@Qb
        Gram=Qb@Qb.T; P=Qb.T@np.linalg.inv(Gram)@Qb
        w=((A@Qtp)**2).sum() + ((C@Qtp@(np.eye(n)-P))**2).sum()
        wmin=min(wmin,w)
        if w<1e-12: zeros+=1
    return wmin,zeros
for (M0,M1,t,n,name) in [(2,2,1,2,"(2,2,2,2) t=1"),(4,4,2,4,"(4,4,4,4) t=2"),(3,3,2,3,"(3,3,3,3) t=2")]:
    wmin,z=wcore(M0,M1,t,n)
    print(f"{name}: min core w over 2000 configs = {wmin:.3e}, #(w<1e-12)={z}  => w>0 a.e. (core positive)")
print("\n(core w=0 only where Q̃_p=0, a proper polynomial locus => NULL; the atom's w>0 holds a.e.)")
