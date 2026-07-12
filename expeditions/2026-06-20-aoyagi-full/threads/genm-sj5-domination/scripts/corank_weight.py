import numpy as np

# Corank weight W(t) = ∫_{A_cor in [-1,1]^{b×M2}} det(A_cor G A_cor^T)^{-a/2} dA_cor
# G = diag(1,...,1, t^2)  (M2 eigenvalues; smallest = t^2, first-order tail rank-drop)
# Extract the t->0 exponent p_W by log-log slope; detect log by curvature.
rng = np.random.default_rng(0)

def W_of_t(a, b, M2, t, N=4_000_000):
    # Monte-Carlo over box [-1,1]^{b*M2}; volume factor = 2^{b*M2}
    A = rng.uniform(-1, 1, size=(N, b, M2))
    sig2 = np.ones(M2); sig2[-1] = t*t
    # M = A * diag(sig2) * A^T  (b×b) per sample
    # A_scaled columns by sig2: (A * sig2) then A^T
    As = A * sig2[None, None, :]
    Gr = np.einsum('nik,njk->nij', As, A)  # b×b
    if b == 1:
        val = Gr[:, 0, 0]
        dets = val
    else:
        dets = np.linalg.det(Gr)
    dets = np.clip(dets, 1e-300, None)
    integrand = dets**(-a/2.0)
    vol = 2.0**(b*M2)
    return integrand.mean()*vol

def exponent(a, b, M2, ts=(1e-1,1e-2,1e-3,1e-4,1e-5)):
    ts = np.array(ts)
    Ws = np.array([W_of_t(a,b,M2,t) for t in ts])
    logt = np.log(ts); logW = np.log(Ws)
    # slope between consecutive points
    slopes = np.diff(logW)/np.diff(logt)   # p_W ~ -slope
    return Ws, -slopes

print("format: (a,b,M2)  predicted p_W=max(0,a-(M2-1)) [b=1]  |  W(t) values  |  measured -slopes")
for (a,b,M2) in [(1,1,2),(1,1,3),(2,1,2),(2,1,3),(3,1,2),(3,1,3),(1,2,3),(2,2,3),(1,2,2),(2,2,4)]:
    Ws, sl = exponent(a,b,M2)
    pred = max(0, a-(M2-1)) if b==1 else None
    print(f"({a},{b},{M2})  pred_b1={pred}  W={np.array2string(Ws,precision=3)}  -slopes={np.array2string(sl,precision=3)}")
