#!/usr/bin/env python3
"""Monte-Carlo RLCT estimate via small-ball volume scaling: V(t)=P(loss<t) ~ t^lambda |log t|^{m-1}.
Estimate lambda = local slope of log V(t) vs log t at small t (multiplicity m inflates via log-log,
so we fit lambda + (m-1)*loglog correction). GUIDE ONLY (float) -- calibrated on sum-of-squares."""
import numpy as np

rng = np.random.default_rng(0)

def est_lambda(loss_fn, dim, N=4000000, sigma=1.0, ts=None, verbose=True, label=""):
    X = rng.normal(0, sigma, size=(N, dim))
    L = loss_fn(X)                       # loss at each sample (>=0)
    L = np.sort(L)
    if ts is None:
        # geometric grid of thresholds in the small-loss regime
        ts = np.exp(np.linspace(np.log(L[50]), np.log(np.quantile(L,0.05)), 12))
    logV=[]; logt=[]
    for t in ts:
        V = np.count_nonzero(L < t)/N
        if V>0:
            logV.append(np.log(V)); logt.append(np.log(t))
    logV=np.array(logV); logt=np.array(logt)
    # slope over the smallest-t half (cleanest power law; ignore log-log for a first read)
    k = len(logt)//2
    A = np.polyfit(logt[:max(k,3)], logV[:max(k,3)], 1)
    lam = A[0]
    if verbose:
        print(f"  [{label}] dim={dim} N={N}: slope(logV/logt) small-t = {lam:.3f}")
    return lam

# ---- calibration: sum of k squares -> rlct = k/2 ----
for k in [3,4,6,8]:
    est_lambda(lambda X: (X[:, :k]**2).sum(1), dim=k, N=2000000, label=f"sum {k} sq (expect {k/2})")

def dln_loss(dims):
    """loss = ||C1 C2 ... ||^2, dims=(M1,...,M_{L+1}); C_i is M_i x M_{i+1}."""
    shapes=[(dims[i],dims[i+1]) for i in range(len(dims)-1)]
    sizes=[a*b for a,b in shapes]; dim=sum(sizes)
    off=np.cumsum([0]+sizes)
    def f(X):
        N=X.shape[0]; P=None
        for i,(a,b) in enumerate(shapes):
            Ci=X[:,off[i]:off[i+1]].reshape(N,a,b)
            P=Ci if P is None else P@Ci
        return (P.reshape(N,-1)**2).sum(1)
    return f, dim

print("---- DLN cores (expect rlct = minAdm/2) ----")
for dims,exp in [((2,2,2),1.5),((3,3,4),4.0),((2,2,2,2),1.5),((3,3,2,2),2.0),((2,2,2,2,2),None)]:
    f,dim=dln_loss(dims)
    est_lambda(f,dim,N=4000000,sigma=1.0,label=f"DLN {dims} expect {exp}")
