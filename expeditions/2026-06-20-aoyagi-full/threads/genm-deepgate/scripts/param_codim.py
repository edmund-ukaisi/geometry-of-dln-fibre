"""
Exact-ish parameter-space codimension of  { rank(L_1 L_2 ... L_p) <= s }  for generic layers.

Deep factor Z = L_1 ... L_p,  L_i : v_{i-1} x v_i  (widths v_0..v_p).
This is a quiver composite-rank locus; its param-space codim can be BELOW the determinantal
codim (v_0-s)(v_p-s) because of ALIGNED components (im L_{i+1} in ker L_i etc.).

METHOD (L-rank / normal-projection): at a point p on {rank Z = s} the codim of the component
through p equals rank of the linear map
    Phi_p : (dL_1,...,dL_p)  |->  U^T ( sum_i L_1..L_{i-1} dL_i L_{i+1}..L_p ) V
where U = left-null(Z) (v0 x (v0-s)), V = right-null(Z) (vp x (vp-s)).
The variety codim = MIN over components; we probe a battery of constructed points and take the min.

Validation: exact 2-layer DP formula + determinantal single-matrix case.
"""
import numpy as np
import itertools, random

def rank_np(A, tol=1e-7):
    if A.size == 0: return 0
    s = np.linalg.svd(A, compute_uv=False)
    if s.size == 0: return 0
    return int((s > tol*max(1.0, s[0])).sum())

def product(layers):
    Z = layers[0]
    for L in layers[1:]:
        Z = Z @ L
    return Z

def phi_rank(layers, s, tol=1e-7):
    """codim of the component of {rank Z <= s} through this point (must have rank Z == s)."""
    p = len(layers)
    Z = product(layers)
    v0, vp = Z.shape
    r = rank_np(Z, tol)
    if r != s:
        return None  # point not on the target stratum
    # left null (U): columns span {x : x^T Z = 0} = null(Z^T)
    Uu, Su, Vt = np.linalg.svd(Z)
    # left singular vectors beyond rank -> left null space
    U = Uu[:, s:]              # v0 x (v0-s)
    V = Vt[s:, :].T           # vp x (vp-s)
    # build Phi matrix: rows index (i, entry of dL_i); output = flatten(U^T dZ V) in R^{(v0-s)(vp-s)}
    rows = []
    for i in range(p):
        vi_1, vi = layers[i].shape
        # prefix = L_1..L_{i-1}, suffix = L_{i+1}..L_p
        pre = np.eye(v0)
        for j in range(i):
            pre = pre @ layers[j]        # v0 x v_{i-1}... actually pre = product(L_1..L_i) shape v0 x v_i
        # recompute prefixes properly:
        pre = np.eye(layers[0].shape[0])
        for j in range(i):
            pre = pre @ layers[j]        # shape v0 x v_{i-1}
        suf = np.eye(layers[-1].shape[1])
        for j in range(p-1, i, -1):
            suf = layers[j] @ suf        # shape v_i x vp
        # dZ for unit dL_i at (a,b): pre[:,a] outer suf[b,:]
        for a in range(vi_1):
            for b in range(vi):
                dZ = np.outer(pre[:, a], suf[b, :])   # v0 x vp
                proj = U.T @ dZ @ V                     # (v0-s) x (vp-s)
                rows.append(proj.flatten())
    Phi = np.array(rows)
    return rank_np(Phi, tol)

def rand_full(m, n, rng, lo=-5, hi=5):
    while True:
        A = rng.integers(lo, hi+1, size=(m,n)).astype(float)
        if rank_np(A) == min(m,n):
            return A

def rand_rank(m, n, r, rng, lo=-5, hi=5):
    if r == 0: return np.zeros((m,n))
    P = rand_full(m, r, rng); Q = rand_full(r, n, rng)
    return P @ Q

def constructed_points(widths, s, rng, ntry=3):
    """battery of points on {rank Z = s}: single-edge drops + waist/core factorizations."""
    v = widths; p = len(v)-1
    pts = []
    # (A) single-edge drop: layer i rank s, others full
    for i in range(p):
        for _ in range(ntry):
            layers = [rand_full(v[j], v[j+1], rng) for j in range(p)]
            layers[i] = rand_rank(v[i], v[i+1], s, rng)
            if rank_np(product(layers)) == s:
                pts.append(layers)
    # (B) waist at edge e (0..p): force composite through rank-s core placed at edge e
    #     L_1..L_e generic to width v_e, then rank-s bottleneck into the rest
    for e in range(0, p+1):
        for _ in range(ntry):
            layers = [rand_full(v[j], v[j+1], rng) for j in range(p)]
            # inject a rank-s cut across edge e by replacing near e:
            # make the map from v_e-space rank s by putting a rank-s factor into layer e (0-indexed edge -> layer e index e)
            # Simplest generic aligned: pick a rank-s projector on width v_e and thread it.
            # Realise: choose core C0 = rand_rank at the narrowest, spread.
            # Use: layer at index min(e,p-1) set to rank s but keep neighbors generic (approx aligned)
            idx = min(max(e-1,0), p-1)
            layers[idx] = rand_rank(v[idx], v[idx+1], s, rng)
            if rank_np(product(layers)) == s:
                pts.append(layers)
    # (C) global core: Z0 = rank-s, thread [P|0]...[Q;0]
    for _ in range(ntry):
        if s <= min(v):
            P = rand_full(v[0], s, rng) if s>0 else np.zeros((v[0], max(s,1)))
            Q = rand_full(s, v[-1], rng) if s>0 else np.zeros((max(s,1), v[-1]))
            layers=[]
            # L_1 = [P | 0] : v0 x v1
            L1 = np.zeros((v[0], v[1]));
            if s>0: L1[:, :s] = P
            layers.append(L1)
            for j in range(1, p-1):
                Lj = np.zeros((v[j], v[j+1]))
                m = min(s, v[j], v[j+1])
                for t in range(m): Lj[t,t]=1.0
                layers.append(Lj)
            if p>=2:
                Lp = np.zeros((v[p-1], v[p]))
                if s>0: Lp[:s,:] = Q
                layers.append(Lp)
            if rank_np(product(layers))==s:
                pts.append(layers)
    return pts

def param_codim(widths, s, seed=0, ntry=4):
    rng = np.random.default_rng(seed)
    v = widths; p = len(v)-1
    if p == 1:
        # single matrix: determinantal, exact
        return (v[0]-s)*(v[1]-s)
    best = None
    pts = constructed_points(widths, s, rng, ntry=ntry)
    for layers in pts:
        c = phi_rank(layers, s)
        if c is not None:
            if best is None or c < best:
                best = c
    return best

# ---- validation: exact 2-layer DP ----
def two_layer_codim_exact(v0,v1,v2,s):
    best=None
    for r1 in range(0, min(v0,v1)+1):
      for r2 in range(0, min(v1,v2)+1):
        g0 = max(0, r2 - r1)
        gmin = max(g0, r2 - s)         # need composite rank r2-g <= s => g >= r2-s
        gmax = min(r2, v1-r1)
        for g in range(gmin, gmax+1):
            c1=(v0-r1)*(v1-r1)
            c2=(v1-r2)*(v2-r2)
            # incidence: two subspaces dim (v1-r1) [ker L1] and r2 [im L2] in R^{v1}, intersection >= g
            alpha=r2; beta=v1-r1
            cinc=(g-g0)*(v1-alpha-beta+g)
            c=c1+c2+cinc
            if best is None or c<best: best=c
    return best

if __name__=="__main__":
    print("=== validation ===")
    # (2,2,2) s=0 : expect 3 (aligned), single-edge would be 4
    print("(2,2,2) s=0: L-rank param =", param_codim((2,2,2),0), " DPexact =", two_layer_codim_exact(2,2,2,0), " det=",(2-0)*(2-0))
    print("(2,2,2) s=1: L-rank param =", param_codim((2,2,2),1), " DPexact =", two_layer_codim_exact(2,2,2,1), " det=",(2-1)*(2-1))
    print("(4,2,4) s=0: L-rank param =", param_codim((4,2,4),0), " DPexact =", two_layer_codim_exact(4,2,4,0), " det=",(4)*(4))
    print("(4,2,4) s=1: L-rank param =", param_codim((4,2,4),1), " DPexact =", two_layer_codim_exact(4,2,4,1), " det=",(3)*(3))
    print("(4,4,4) s=0: L-rank param =", param_codim((4,4,4),0), " DPexact =", two_layer_codim_exact(4,4,4,0), " det=",16)
    print("(4,4,4) s=1: L-rank param =", param_codim((4,4,4),1), " DPexact =", two_layer_codim_exact(4,4,4,1), " det=",9)
    print("(4,4,4) s=2: L-rank param =", param_codim((4,4,4),2), " DPexact =", two_layer_codim_exact(4,4,4,2), " det=",4)
    print("(4,4,4) s=3: L-rank param =", param_codim((4,4,4),3), " DPexact =", two_layer_codim_exact(4,4,4,3), " det=",1)
    print("(3,4,3,4) s: check vs single matrix determinantal-shape (arity via 3 layers)")
    for s in range(0,3):
        print(f"   (3,4,3) s={s}: L-rank={param_codim((3,4,3),s)} DP={two_layer_codim_exact(3,4,3,s)} det={(3-s)*(3-s)}")
    print("(5,3,5) rho=3:")
    for s in range(0,3):
        print(f"   s={s}: L-rank={param_codim((5,3,5),s)} DP={two_layer_codim_exact(5,3,5,s)} det={(5-s)*(5-s)}")
