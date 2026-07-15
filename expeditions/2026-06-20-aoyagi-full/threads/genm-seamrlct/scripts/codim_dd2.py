import numpy as np
rng=np.random.default_rng(0)
def mu_flat(P,H,F,E):
    FE=F@E; X=np.concatenate([H,FE],axis=1); return (P@X).ravel()
def jac_rank(P,H,F,E,eps=1e-6):
    x0=mu_flat(P,H,F,E); cols=[]
    arrs=[P,H,F,E]
    for ai,arr in enumerate(arrs):
        for idx in np.ndindex(arr.shape):
            a2=arr.copy(); a2[idx]+=eps
            args=list(arrs); args[ai]=a2
            cols.append((mu_flat(*args)-x0)/eps)
    return np.linalg.matrix_rank(np.array(cols).T, tol=1e-4)
ranks=[]
for _ in range(3000):
    mech=rng.integers(0,5)
    P=rng.normal(size=(2,3)); H=rng.normal(size=(3,2)); F=rng.normal(size=(3,1)); E=rng.normal(size=(1,2))
    if mech==0:      # E=0
        E=np.zeros((1,2)); H=np.zeros((3,2))  # PH=0 too via H in kerP? just H=0
    if mech==0:      # E=0 & H columns in ker P (P generic rank2)
        ns=np.linalg.svd(P)[2][-1]; H=np.outer(ns,rng.normal(size=2)); E=np.zeros((1,2))
    elif mech==1:    # P rank1 -> big kernel(2d); [H|FE] cols in it
        u=rng.normal(size=2); v=rng.normal(size=3); P=np.outer(u,v)  # rank1
        K=np.linalg.svd(P)[2][1:].T   # 3x2 kernel basis
        H=K@rng.normal(size=(2,2)); F=K@rng.normal(size=(2,1)); E=rng.normal(size=(1,2))
    elif mech==2:    # P generic rank2, [H|FE] all cols in kerP (1d)
        ns=np.linalg.svd(P)[2][-1]; c=rng.normal(size=4); X=np.outer(ns,c)
        H=X[:,:2]; FE=X[:,2:]; U,s,Vt=np.linalg.svd(FE); F=(U[:,:1]*s[0]).reshape(3,1); E=Vt[:1,:]
    elif mech==3:    # F=0 (FE=0) and PH=0
        F=np.zeros((3,1)); ns=np.linalg.svd(P)[2][-1]; H=np.outer(ns,rng.normal(size=2))
    elif mech==4:    # E=0 and P H=0 with H rank1 in kerP
        ns=np.linalg.svd(P)[2][-1]; H=np.outer(ns,rng.normal(size=2)); E=np.zeros((1,2)); F=rng.normal(size=(3,1))
    if not np.allclose(mu_flat(P,H,F,E),0,atol=1e-7): continue
    ranks.append(jac_rank(P,H,F,E))
ranks=np.array(ranks)
print("Jacobian-rank (=local codim) distribution at sampled smooth zeros:")
vals,cts=np.unique(ranks,return_counts=True)
for v,c in zip(vals,cts): print(f"   codim={v}: {c}   -> codim/2={v/2}")
print(f"   MIN codim over components = {ranks.min()}  => rlct should be {ranks.min()/2} if benign")
print(f"   (IS rlct read ~2.22-2.34)")
