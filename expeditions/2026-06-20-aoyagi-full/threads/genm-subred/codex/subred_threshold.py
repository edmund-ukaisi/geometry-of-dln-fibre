import numpy as np
rng = np.random.default_rng(1)

# lct estimator: vol{ det(QbQb^T) < eps } ~ eps^{lct(det)}  as eps->0.
# integrand det^{-a/2} finite  <=>  a/2 < lct(det)  <=>  a < 2*lct(det).
# Report thr := 2*lct(det)  (the 'a' threshold).
def gram_det(Qb):
    G = Qb @ Qb.T
    return np.linalg.det(G)

def est_2lct(sampler, N=4_000_000):
    # slope of log P(det<eps) vs log eps over a small-eps window -> lct(det).
    d = sampler(N)
    d = d[d>0]
    # use quantile-based scaling: log(eps) vs log(cumfrac)
    eps_grid = np.array([1e-2,1e-3,1e-4,1e-5,1e-6,1e-7,1e-8])
    fr = np.array([(d<e).mean() for e in eps_grid])
    ok = fr>50/len(d)
    le, lf = np.log(eps_grid[ok]), np.log(fr[ok])
    if len(le)<3: return np.nan
    slope = np.polyfit(le[-4:], lf[-4:],1)[0]  # ~ lct(det)
    return 2*slope

# free single-layer (b,q): Qb free b x q in box.  2*lct should be q-b+1.
def free_sampler(b,q):
    def s(N):
        Q = rng.uniform(-1,1,size=(N,b,q))
        G = np.einsum('nij,nkj->nik',Q,Q)
        return np.abs(np.linalg.det(G))
    return s

# two-layer (b,m,q): Qb = Y@A,  Y: b x m, A: m x q, box.
def prod_sampler(b,m,q):
    def s(N):
        Y = rng.uniform(-1,1,size=(N,b,m))
        A = rng.uniform(-1,1,size=(N,m,q))
        Q = np.einsum('nij,njk->nik',Y,A)
        G = np.einsum('nij,nkj->nik',Q,Q)
        return np.abs(np.linalg.det(G))
    return s

print("CALIBRATION free (b,q): est 2*lct  vs  q-b+1")
for (b,q) in [(1,2),(1,3),(2,3),(2,4),(1,4)]:
    print(f"  free (b={b},q={q}): est={est_2lct(free_sampler(b,q)):.3f}  free q-b+1={q-b+1}")

print()
print("TWO-LAYER product (b,m,q): est 2*lct  vs  free(q-b+1)  vs  twist(min(m,q)-b+1)")
cases = [(1,2,2),(1,1,2),(1,2,3),(1,3,2),(2,3,3),(2,2,3),(2,3,2),(1,1,3),(1,3,1)]
for (b,m,q) in cases:
    e = est_2lct(prod_sampler(b,m,q))
    free = q-b+1
    twist = min(m,q)-b+1
    print(f"  (b={b},m={m},q={q}): est={e:.3f}   free(q-b+1)={free}   twist(min(m,q)-b+1)={twist}")
