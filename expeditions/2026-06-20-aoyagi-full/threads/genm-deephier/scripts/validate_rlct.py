"""
Direct RLCT validation of the honest deep local integral (loss-only, full-collapse of single deep matrix).
loss = ||F A2||_F^2 , F in R^{u x M2}, A2 in R^{M2 x n}, both near 0.
RLCT lambda = tail exponent of P(loss < t) ~ t^lambda as t->0.  C_hier = 2*lambda.
Predicted (hierarchical LP): C=10 -> lambda=5.  Single-scale naive: C=12 -> lambda=6.
Also compares the SINGLE-SCALE model (A2 = s * fixed_unit_matrix, one radial scale) vs FULL (A2 free).
"""
import numpy as np

def tail_exponent(losses, ts):
    """estimate lambda from P(loss<t) ~ t^lambda via slope of log P vs log t over small t."""
    N=len(losses)
    logs=[]; logt=[]
    for t in ts:
        P=np.mean(losses<t)
        if P>0:
            logs.append(np.log(P)); logt.append(np.log(t))
    logs=np.array(logs); logt=np.array(logt)
    # linear fit slope
    A=np.vstack([logt,np.ones_like(logt)]).T
    slope,intercept=np.linalg.lstsq(A,logs,rcond=None)[0]
    return slope, list(zip([round(np.exp(x),2) for x in logt],[round(np.exp(y),4) for y in logs]))

def full_model(u,M2,n,N=4000000,seed=0,box=1.0):
    rng=np.random.default_rng(seed)
    F=rng.uniform(-box,box,size=(N,u,M2))
    A=rng.uniform(-box,box,size=(N,M2,n))
    FA=np.einsum('nij,njk->nik',F,A)
    loss=(FA**2).sum(axis=(1,2))
    return loss

def single_scale_model(u,M2,n,N=4000000,seed=0,box=1.0):
    """A2 = s * U0 (fixed generic unit matrix), s in (0,box], measure s^{kappa-1}ds (kappa=M2*n).
       loss = s^2 ||F U0||^2. Sample s with density s^{kappa-1}, F in box."""
    rng=np.random.default_rng(seed)
    kappa=M2*n
    U0=rng.standard_normal((M2,n)); U0/=np.linalg.norm(U0)
    # sample s with pdf ~ s^{kappa-1} on (0,box]: s = box * V^{1/kappa}, V~U(0,1)
    V=rng.uniform(0,1,size=N); s=box*V**(1.0/kappa)
    F=rng.uniform(-box,box,size=(N,u,M2))
    FU=np.einsum('nij,jk->nik',F,U0)
    loss=(s**2)*(FU**2).sum(axis=(1,2))
    return loss

if __name__=="__main__":
    u,M2,n=3,4,4    # (4,4,4,4) full collapse; predicted C_hier=10 (lam=5), single-scale=12 (lam=6)
    ts=np.array([0.5,0.2,0.1,0.05,0.02,0.01,0.005,0.002,0.001])
    print("=== (4,4,4,4) full-collapse, loss=||F A2||^2, u=3,M2=4,n=4 ===")
    print(f"  predicted lambda: hierarchical=5.0 (C=10), single-scale=6.0 (C=12)")
    lf=full_model(u,M2,n)
    slope,tab=tail_exponent(lf,ts)
    print(f"  FULL model  (A2 free, honest): tail lambda ~ {slope:.3f}  -> C_hier ~ {2*slope:.2f}")
    print(f"     P(loss<t):",tab)
    ls=single_scale_model(u,M2,n)
    slope2,tab2=tail_exponent(ls,ts)
    print(f"  SINGLE-SCALE (A2=s*U0):        tail lambda ~ {slope2:.3f}  -> C ~ {2*slope2:.2f}")
    print(f"     P(loss<t):",tab2)
