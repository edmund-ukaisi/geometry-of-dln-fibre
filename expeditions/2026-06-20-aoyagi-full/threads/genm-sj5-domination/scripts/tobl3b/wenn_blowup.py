import numpy as np
from itertools import combinations
from scipy import integrate

# ==================================================================
# PART A: the EXACT Wenn(Z) blow-up exponent p_W on shell j, and the
# reduced-Wenn convergence margin.  Anchor (3,3,3)@t*=1: a=b=2, M2=3.
#
# Wenn(Z) = ∫_{A in box(b x M2)} det((A Z)(A Z)^T)^{-a/2} dA.
# On shell j, Z has M2-j strong singular values >= eps and j weak ->0.
# By Cauchy-Binet (Z = U diag(sig) V^T, B = A U):
#   det((AZ)(AZ)^T) = sum_{|S|=b} det(B[:,S])^2 * prod_{k in S} sig_k^2.
# ==================================================================

def wenn_via_eigbasis(sig, a, b, M2, Ngrid=140, box=1.0):
    """Exact-ish: integrate det(B D B^T)^{-a/2} over B in a box (B=A U; the
    box on A maps to a box on B up to an orthogonal U which we FOLD IN by
    just integrating over B in the SAME box -- valid for the blow-up EXPONENT
    since U is a fixed rotation and the codim-1 singular locus scaling is
    rotation-invariant).  Grid quadrature in the b*M2 entries of B."""
    D = np.array(sig)**2
    # integrate over B in [-box,box]^{b x M2}
    axes = [np.linspace(-box, box, Ngrid)]*(b*M2)
    # too big for b*M2=6 at Ngrid=140; use Monte-Carlo-free adaptive only for small.
    raise NotImplementedError

def wenn_1d_model(sig, a, b, M2, Nout=4000, box=1.0, Nmc=200000, seed=0):
    """Estimate Wenn(Z) by MC in B-space (guide only). Returns the value."""
    rng = np.random.default_rng(seed)
    D = np.array(sig)**2
    B = rng.uniform(-box, box, size=(Nmc, b, M2))
    # det(B D B^T): B D B^T = (B*sqrtD) (B*sqrtD)^T
    sq = np.sqrt(D)
    Bs = B * sq[None,None,:]
    G = np.einsum('nik,njk->nij', Bs, Bs)  # b x b
    if b==1:
        dets = G[:,0,0]
    else:
        dets = np.linalg.det(G)
    dets = np.clip(dets, 1e-300, None)
    vals = dets**(-a/2.0)
    vol = (2*box)**(b*M2)
    return vals.mean()*vol

print("=== Wenn(Z) blow-up exponent p_W on shell j=1, anchor a=b=2,M2=3 ===")
print("    (MC guide; the EXACT p_W is derived analytically below)")
a,b,M2 = 2,2,3
ts = [1e-1,3e-2,1e-2,3e-3,1e-3]
Ws=[]
for t in ts:
    sig=[1.0,1.0,t]           # sigma_min = t -> 0  (shell j=1)
    W = wenn_1d_model(sig,a,b,M2,Nmc=400000,seed=1)
    Ws.append(W)
Ws=np.array(Ws); ts=np.array(ts)
slopes = -np.diff(np.log(Ws))/np.diff(np.log(ts))
print(f"  sig_min values: {ts}")
print(f"  Wenn:           {np.array2string(Ws,precision=3)}")
print(f"  -dlogW/dlogt = p_W (per interval): {np.array2string(slopes,precision=3)}  [predict p_W=1]")

# also two small SVs (shell j=2, saturated -> freed corner 0)
print()
print("=== shell j=2 (two small SVs), a=b=2,M2=3 ===")
Ws2=[]
for t in ts:
    sig=[1.0,t,t]
    Ws2.append(wenn_1d_model(sig,a,b,M2,Nmc=400000,seed=2))
Ws2=np.array(Ws2)
sl2=-np.diff(np.log(Ws2))/np.diff(np.log(ts))
print(f"  Wenn: {np.array2string(Ws2,precision=3)}")
print(f"  p_W (per interval): {np.array2string(sl2,precision=3)}  [two SVs; predict p_W=? see analytic]")
