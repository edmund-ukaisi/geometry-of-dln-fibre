"""
Importance-sampled tube-volume RLCT estimator.

Proposal: each coordinate x = sign * 10^{u}, u ~ Uniform(-B,0), sign=+-1 -> concentrates mass near 0
so DEEP degenerations (high codim) are hit. Reweight to the uniform box [-1,1]^D:
   w = prod_coord ( |x_coord| * ln10 * B ).
Estimate P_unif(f<=t) = mean( 1(f<=t) * w ).  vol{f<=t} ~ t^lambda  =>  slope of log P vs log t.
Validated on sum-of-squares (e/2) and matrix products (codim/2).
"""
import numpy as np
from rlct_tools import CR, minAdm

LN10 = np.log(10.0)

def is_sample(shapes, N, rng, B=6.0):
    """Return (list of arrays, logw) under the log-uniform-magnitude proposal on [-1,1] box."""
    arrs = []
    logw = np.zeros(N)
    for sh in shapes:
        d = int(np.prod(sh))
        u = rng.uniform(-B, 0.0, size=(N, d))
        sgn = rng.integers(0, 2, size=(N, d)) * 2 - 1
        x = sgn * (10.0 ** u)
        logw += np.log(np.abs(x) * LN10 * B).sum(axis=1)
        arrs.append(x.reshape((N,) + sh))
    return arrs, logw

def is_rlct(shapes, loss_fn, ts, N=2_000_000, reps=6, B=6.0, seed=0):
    rng = np.random.default_rng(seed)
    num = np.zeros(len(ts)); den = 0.0
    for _ in range(reps):
        arrs, logw = is_sample(shapes, N, rng, B)
        w = np.exp(logw)
        f = loss_fn(arrs)
        den += w.sum()
        for i, t in enumerate(ts):
            num[i] += w[f <= t].sum()
    P = num / den
    ts_a = np.array(ts); m = P > 0
    lam_fit = np.polyfit(np.log(ts_a[m]), np.log(P[m]), 1)[0] if m.sum() >= 2 else float('nan')
    # robust: median of consecutive two-point slopes over the small-t half
    idx = np.where(m)[0]
    slopes = []
    for j in range(len(idx)-1):
        i1, i2 = idx[j], idx[j+1]
        slopes.append((np.log(P[i2])-np.log(P[i1]))/(np.log(ts_a[i2])-np.log(ts_a[i1])))
    slopes = np.array(slopes)
    lam_tail = np.median(slopes[len(slopes)//2:]) if len(slopes) else float('nan')
    return lam_fit, lam_tail, list(zip(ts, P))

def matprod_loss(arrs):
    F, E = arrs
    Z = np.einsum('nij,njk->nik', F, E)
    return (Z**2).sum(axis=(1,2))

def dln_loss_fn(arrs):
    Z = arrs[0]
    for L in arrs[1:]:
        Z = np.einsum('nij,njk->nik', Z, L)
    return (Z**2).sum(axis=(1,2))

if __name__ == "__main__":
    ts = [1e-3,1e-4,1e-5,1e-6,1e-7,1e-8]
    print("VALIDATE: sum of e squares -> e/2")
    for e in [1,2,3,4,5,6]:
        lf, lt, tab = is_rlct([(e,)], lambda a:(a[0]**2).sum(1), ts, N=700_000, reps=3, B=8, seed=1)
        print(f"  e={e}: fit={lf:.3f} tail={lt:.3f}  expect {e/2}")
    print()
    print("VALIDATE: matrix product ||FE||^2 -> codim/2  (F:m x q,E:q x n)")
    print(f"  {'(m,q,n)':>12} {'codim':>6} {'codim/2':>8} {'fit':>7} {'tail':>7}")
    for (m,q,n) in [(2,1,1),(2,2,2),(3,2,3),(2,3,2),(3,3,3),(2,2,3),(4,2,4),(3,2,4),(3,3,2),(4,3,4)]:
        cod = CR((m,q,n),0)
        lf,lt,tab = is_rlct([(m,q),(q,n)], matprod_loss, ts, N=700_000, reps=4, B=8, seed=2)
        flag = "" if abs(lt-cod/2)<0.25 else "  <-- CHECK"
        print(f"  {str((m,q,n)):>12} {cod:>6} {cod/2:>8.2f} {lf:>7.3f} {lt:>7.3f}{flag}")
