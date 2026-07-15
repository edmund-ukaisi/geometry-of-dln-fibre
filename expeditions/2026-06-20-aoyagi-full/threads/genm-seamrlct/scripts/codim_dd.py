import numpy as np
# codim of {P[H|FE]=0}: estimate via rank of Jacobian of mu:(P,H,F,E)->P[H|FE] at MANY random points on
# the zero set (found by projecting), take the codim = max Jacobian rank over sampled smooth points
# (generic component codim = the max rank of d mu over the zero set = codim of the top stratum).
rng=np.random.default_rng(0)
def mu_flat(P,H,F,E):
    FE=F@E; X=np.concatenate([H,FE],axis=1); return (P@X).ravel()
def jac_rank(P,H,F,E,eps=1e-6):
    x0=mu_flat(P,H,F,E); cols=[]
    for arr in (P,H,F,E):
        for idx in np.ndindex(arr.shape):
            a2=arr.copy(); a2[idx]+=eps
            args=[P,H,F,E]; args[[id(P),id(H),id(F),id(E)].index(id(arr))]=a2
            cols.append((mu_flat(*args)-x0)/eps)
    J=np.array(cols).T
    return np.linalg.matrix_rank(J,tol=1e-4)
# Find zeros: set P with kernel k, put all columns of [H|FE] into ker P.
best=0
for _ in range(4000):
    # component: P rank2 (2x3), [H|FE] columns in ker(P) (1-dim). ker of random 2x3:
    P=rng.normal(size=(2,3))
    ns=np.linalg.svd(P)[2][-1]      # kernel vector (3,)
    c=rng.normal(size=4)            # [H|FE]=ns outer c  -> rank1, cols in kerP
    X=np.outer(ns,c)                # 3x4
    H=X[:,:2]; FE=X[:,2:]
    # need FE=F E with F 3x1,E1x2: FE rank<=1 -> ok, factor
    U,s,Vt=np.linalg.svd(FE); F=(U[:,:1]*s[0]); E=Vt[:1,:]
    F=F.reshape(3,1)
    assert np.allclose(mu_flat(P,H,F,E),0,atol=1e-8)
    r=jac_rank(P,H,F,E); best=max(best,r)
print("component-1 (P rank2, [H|FE] in kerP) codim(top)=",best, " codim/2=",best/2)
# other component: [H|FE] free small, P=0 region etc -- min over components is what matters for rlct.
