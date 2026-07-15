import numpy as np
rng = np.random.default_rng(1)

# M=(3,3,4,3), u=2, a=b=1 : M'=(2,4,3). Loss = ||A0' @ A2||^2, A0':2x4, A2:4x3.
# comparator RLCT (unweighted) should be minAdm(M')/2 = 3.
# reduced-G-bound weight = det(A2^T A2)^{-b/2} = det(A2^T A2)^{-1/2}.
# Estimate weighted small-ball exponent lambda: V_w(eps)=E[ w * 1(loss<eps) ] ~ eps^lambda  =>  lambda = RLCT threshold.
u,M2,n = 2,4,3
b = 1
def sample(N):
    A0 = rng.standard_normal((N,u,M2))
    A2 = rng.standard_normal((N,M2,n))
    prod = A0 @ A2                       # N x u x n
    loss = np.sum(prod*prod,axis=(1,2))  # ||A0 A2||^2
    G = np.transpose(A2,(0,2,1)) @ A2    # A2^T A2 : N x n x n
    detGp = np.linalg.det(G)             # pseudo-det (n x n), generically >0
    w = detGp**(-b/2.0)
    return loss, w

N = 6_000_000
loss, w = sample(N)
# density near loss=0: importance-sample by using Gaussian params (standard). Estimate cumulative
# V(eps)=E[w*1(loss<eps)] over Gaussian measure (finite ref measure). Fit slope of log V vs log eps.
eps_list = np.array([0.5,0.25,0.125,0.0625,0.03125,0.015625,0.0078125])
def fit(loss,w,label):
    Vs=[]
    for e in eps_list:
        Vs.append(np.mean(w*(loss<e)))
    Vs=np.array(Vs)
    # slope in log-log (use last points, small eps)
    lg=np.log(eps_list); lV=np.log(Vs)
    # local slopes
    sl=(lV[1:]-lV[:-1])/(lg[1:]-lg[:-1])
    print(f"{label}: V(eps)=",np.round(Vs,6))
    print(f"   local slopes (->lambda):",np.round(sl,3))
    return sl[-1]
lam_w = fit(loss,w,"WEIGHTED det(A2^TA2)^{-1/2}")
lam_u = fit(loss,np.ones_like(w),"UNWEIGHTED (comparator)")
print()
print("Unweighted small-ball exponent ~ RLCT(loss)/ (loss is squared, exponent counts loss^1) -> threshold in q is this value.")
print("comparator threshold minAdm(M')/2 =", 3.0, " ; T1_q =", 2.5)
print("If weighted exponent < unweighted, residual LOWERS the descent threshold (gap risk).")
