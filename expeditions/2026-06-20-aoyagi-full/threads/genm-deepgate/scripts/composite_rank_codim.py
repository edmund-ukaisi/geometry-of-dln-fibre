"""
Exact parameter-space codim of { rank(L_1 ... L_p) <= s } for generic layers, widths v_0..v_p.

Recursion (stratify by rank of the LAST layer r; restricting the head-composite to a generic
r-dim input subspace = replacing the last width by r):
  CR((v0,...,vp), s) = min_{0<=r<=min(v_{p-1},v_p)} [ (v_{p-1}-r)(v_p-r) + CR((v0,...,v_{p-2}, r), s) ]
  base CR((v0,v1), s) = (v0-s)_+ (v1-s)_+   [single matrix rank<=s; 0 if s>=min(v0,v1)]
  and if the reduced target width r <= s, the head sub-chain composite has rank <= r <= s
  automatically -> inner CR = 0.

Validated below:
 - CR(chain, 0) must equal minAdm(chain)  (both = codim{composite=0}).
 - CR two-layer matches the direct stratification min_r[(v1-r)(v2-r)+(v0-s)_+ (r-s)_+].
 - CR vs an independent optimization+L-rank numeric codim on 3-layer cases.
"""
from functools import lru_cache
import numpy as np

@lru_cache(maxsize=None)
def CR(widths, s):
    v = tuple(widths)
    if len(v) == 2:
        v0, v1 = v
        if s >= min(v0, v1):
            return 0
        return (v0 - s) * (v1 - s)
    # stratify by rank r of last layer (v[-2] x v[-1])
    vpm1, vp = v[-2], v[-1]
    best = None
    for r in range(0, min(vpm1, vp) + 1):
        outer = (vpm1 - r) * (vp - r)
        if r <= s:
            inner = 0                      # head composite rank <= r <= s automatically
        else:
            inner = CR(v[:-2] + (r,), s)
        val = outer + inner
        if best is None or val < best:
            best = val
    return best

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 2:
        return M[0]*M[1]
    m0, m1 = M[0], M[1]; rest = M[2:]
    best = None
    for t in range(0, min(m0, m1)+1):
        val = (m0-t)*(m1-t) + minAdm((t,)+rest)
        if best is None or val < best: best = val
    return best

# ---- independent numeric check: optimization landing + L-rank ----
def rank_np(A, tol=1e-8):
    if A.size == 0: return 0
    s = np.linalg.svd(A, compute_uv=False)
    return int((s > tol*max(1.0, s[0])).sum()) if s.size else 0

def product(layers):
    Z = layers[0]
    for L in layers[1:]: Z = Z @ L
    return Z

def phi_codim(layers, s, tol=1e-7):
    Z = product(layers)
    if rank_np(Z, tol) != s: return None
    v0, vp = Z.shape
    Uu,_,Vt = np.linalg.svd(Z)
    U = Uu[:, s:]; V = Vt[s:, :].T
    p = len(layers); rows=[]
    for i in range(p):
        pre = np.eye(layers[0].shape[0])
        for j in range(i): pre = pre @ layers[j]
        suf = np.eye(layers[-1].shape[1])
        for j in range(p-1, i, -1): suf = layers[j] @ suf
        m,n = layers[i].shape
        for a in range(m):
            for b in range(n):
                dZ = np.outer(pre[:,a], suf[b,:])
                rows.append((U.T @ dZ @ V).flatten())
    return rank_np(np.array(rows), tol)

def optimize_land(widths, s, rng, iters=4000, lr=0.03):
    """Adam descent on sum of squared tail singular values to land on {rank Z = s}."""
    v = widths; p = len(v)-1
    L = [rng.standard_normal((v[i], v[i+1]))*0.6 for i in range(p)]
    mI=[np.zeros_like(x) for x in L]; vI=[np.zeros_like(x) for x in L]
    b1,b2,eps=0.9,0.999,1e-8
    for t in range(1, iters+1):
        Z = product(L)
        Uu,S,Vt = np.linalg.svd(Z)
        # objective f = sum_{i>=s} S_i^2 ; grad wrt Z = 2 * U diag(S_i for i>=s, else 0) Vt
        Smask = S.copy()
        for i in range(len(S)):
            if i < s: Smask[i]=0.0
        m,n = Z.shape
        D = np.zeros((m,n))
        for i in range(len(Smask)): D[i,i]=Smask[i]
        gЗ = 2.0*(Uu @ D @ Vt)
        # backprop to each layer
        grads=[]
        for i in range(p):
            pre = np.eye(v[0])
            for j in range(i): pre = pre @ L[j]
            suf = np.eye(v[-1])
            for j in range(p-1, i, -1): suf = L[j] @ suf
            grads.append(pre.T @ gЗ @ suf.T)
        for i in range(p):
            mI[i]=b1*mI[i]+(1-b1)*grads[i]; vI[i]=b2*vI[i]+(1-b2)*grads[i]**2
            mh=mI[i]/(1-b1**t); vh=vI[i]/(1-b2**t)
            L[i]=L[i]-lr*mh/(np.sqrt(vh)+eps)
    return L

def numeric_codim(widths, s, restarts=8, seed=0):
    rng=np.random.default_rng(seed); best=None
    for k in range(restarts):
        L=optimize_land(widths,s,rng)
        Z=product(L)
        if rank_np(Z,1e-5)==s:
            c=phi_codim(L,s,tol=1e-5)
            if c is not None and (best is None or c<best): best=c
    return best

if __name__=="__main__":
    print("=== CR(chain,0) vs minAdm (must be EQUAL) ===")
    chains=[(2,2,2),(4,2,4),(4,4,4),(3,4,3),(5,3,5),(3,3,3,3),(4,4,4,4),(3,4,3,4),(5,4,3,4,5),(4,3,5,3,4),(6,4,4,4,6)]
    ok=True
    for c in chains:
        a=CR(c,0); b=minAdm(c)
        flag="OK" if a==b else "**MISMATCH**"
        if a!=b: ok=False
        print(f"  {c}: CR0={a}  minAdm={b}  {flag}")
    print("ALL CR0==minAdm:", ok)

    print("\n=== CR general-s vs 2-layer direct stratification (must match) ===")
    def two(v0,v1,v2,s):
        return min((v1-r)*(v2-r)+max(0,v0-s)*max(0,r-s) for r in range(0,min(v1,v2)+1))
    for (v0,v1,v2) in [(4,4,4),(2,2,2),(4,2,4),(5,3,5),(3,4,5)]:
        for s in range(0, min(v0,v1,v2)):
            a=CR((v0,v1,v2),s); b=two(v0,v1,v2,s)
            print(f"  ({v0},{v1},{v2}) s={s}: CR={a} direct={b} {'OK' if a==b else '**MISMATCH**'}")

    print("\n=== CR vs numeric optimization+L-rank (3-layer, general s) ===")
    for (widths, s) in [((3,3,3,3),0),((3,3,3,3),1),((3,3,3,3),2),((4,3,4,3),1),((4,3,4,3),2),
                        ((4,4,4,4),0),((4,4,4,4),1),((4,4,4,4),2),((4,4,4,4),3),((5,3,4,3),1)]:
        cr=CR(widths,s); nc=numeric_codim(widths,s,restarts=10)
        print(f"  {widths} s={s}: CR={cr}  numeric={nc}  {'OK' if cr==nc else '  <-- check'}")
