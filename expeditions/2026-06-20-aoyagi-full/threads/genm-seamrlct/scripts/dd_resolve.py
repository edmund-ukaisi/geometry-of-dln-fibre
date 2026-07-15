import numpy as np
rng=np.random.default_rng(3)
def mu_flat(P,H,F,E):
    FE=F@E; X=np.concatenate([H,FE],axis=1); return (P@X).ravel()
def jac_rank(P,H,F,E,eps=1e-6):
    x0=mu_flat(P,H,F,E); cols=[]; arrs=[P,H,F,E]
    for ai,arr in enumerate(arrs):
        for idx in np.ndindex(arr.shape):
            a2=arr.copy(); a2[idx]+=eps; args=list(arrs); args[ai]=a2
            cols.append((mu_flat(*args)-x0)/eps)
    return np.linalg.matrix_rank(np.array(cols).T, tol=1e-4)

# EXHAUSTIVE component search: random zeros via many mechanisms incl. combined rank drops
mins=99
for _ in range(20000):
    P=rng.normal(size=(2,3)); H=rng.normal(size=(3,2)); F=rng.normal(size=(3,1)); E=rng.normal(size=(1,2))
    m=rng.integers(0,8)
    if m==0: E[:]=0                                   # FE=0, then need PH=0
    if m in (0,5): 
        ns=np.linalg.svd(P)[2][-1]; H=np.outer(ns,rng.normal(size=2))
    if m==1: F[:]=0; ns=np.linalg.svd(P)[2][-1]; H=np.outer(ns,rng.normal(size=2))
    if m==2:  # P rank1
        P=np.outer(rng.normal(size=2),rng.normal(size=3)); K=np.linalg.svd(P)[2][1:].T
        H=K@rng.normal(size=(2,2)); F=K@rng.normal(size=(2,1))
    if m==3:  # E=0 and H one column in kerP, other free-but-in kerP
        ns=np.linalg.svd(P)[2][-1]; H=np.outer(ns,rng.normal(size=2)); E[:]=0
    if m==4:  # P generic; H col1 in kerP, FE=0
        ns=np.linalg.svd(P)[2][-1]; h1=ns*rng.normal(); H=np.column_stack([h1,rng.normal(size=3)]); 
        # need P*H col2 =0 too -> both in kerP
        H=np.outer(ns,rng.normal(size=2)); F[:]=0
    if m==6:  # only E small (rank of FE via E), H in kerP entirely, F generic
        ns=np.linalg.svd(P)[2][-1]; H=np.outer(ns,rng.normal(size=2)); 
        # FE must be in kerP: FE=F E, choose E so that F E in span ns? F generic 3x1, E 1x2 -> FE=F(E) rank1 col-space=span F
        # need span F subset kerP -> F=ns*scal
        F=(ns*rng.normal()).reshape(3,1)
    if m==7:  # P rank1 AND E=0
        P=np.outer(rng.normal(size=2),rng.normal(size=3)); K=np.linalg.svd(P)[2][1:].T
        H=K@rng.normal(size=(2,2)); E[:]=0
    if np.allclose(mu_flat(P,H,F,E),0,atol=1e-7):
        r=jac_rank(P,H,F,E); mins=min(mins,r)
print("MIN component codim found =",mins,"  codim/2 =",mins/2)

# Reliable rlct with convergence diagnostic (tail slopes at shrinking t)
LN10=np.log(10.0)
def is_rlct_conv(shapes, loss, B=10.0, N=600_000, reps=10, seed=7):
    ts=10.0**(-np.arange(2,12))   # 1e-2 .. 1e-11
    rng=np.random.default_rng(seed); num=np.zeros(len(ts)); den=0.0
    for _ in range(reps):
        arrs=[]; logw=np.zeros(N)
        for sh in shapes:
            d=int(np.prod(sh)); u=rng.uniform(-B,0,size=(N,d)); s=rng.integers(0,2,size=(N,d))*2-1
            x=s*(10.0**u); logw+=np.log(np.abs(x)*LN10*B).sum(1); arrs.append(x.reshape((N,)+sh))
        w=np.exp(logw); f=loss(arrs); den+=w.sum()
        for i,t in enumerate(ts): num[i]+=w[f<=t].sum()
    P=num/den; msk=P>0; lt=np.log(ts[msk]); lP=np.log(P[msk])
    slopes=np.diff(lP)/np.diff(lt)
    return ts[msk], P[msk], slopes
def ddloss(a):
    P,H,F,E=a; FE=np.einsum('nij,njk->nik',F,E); X=np.concatenate([H,FE],axis=2)
    return (np.einsum('nij,njk->nik',P,X)**2).sum(axis=(1,2))
ts,P,sl=is_rlct_conv([(2,3),(3,2),(3,1),(1,2)], ddloss)
print("t, P, consecutive-slope (rlct estimate; should stabilize at small t):")
for i in range(len(sl)):
    print(f"   t={ts[i]:.0e}->{ts[i+1]:.0e}: P={P[i+1]:.2e} slope={sl[i]:.3f}")
