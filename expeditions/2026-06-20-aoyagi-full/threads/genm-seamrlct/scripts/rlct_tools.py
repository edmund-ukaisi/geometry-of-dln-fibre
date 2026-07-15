"""
RLCT tools for the deep-atlas seam adjudication.

Two engines:
 (E1) EXACT: rlct via the paper's Prop rlct_elem theorems for models that decompose into
      disjoint-variable sums/products of monomials and matrix-product (2-layer DLN) blocks.
      - rlct(F+G) = rlct(F)+rlct(G)          (disjoint vars, F,G>=0)          [S1]
      - rlct(F*G) = min(rlct(F),rlct(G))     (disjoint vars)                  [S2]
      - rlct(sum of e squares) = e/2                                          [S4]
      - rlct(||F E||^2), F:m x q, E:q x n  = minAdm(m,q,n)/2  (cited 2-layer) [BASE]
 (E2) NUMERIC: tube-volume estimator  vol{f<=t} ~ t^lambda (log 1/t)^{m-1}.
      Importance-sample near the zero set; regress log V(t) vs log t at small t.

minAdm / CR = composite-rank codim recursion (deepgate/design).
"""
import numpy as np
from functools import lru_cache

# ---------------------------------------------------------------- CR / minAdm
@lru_cache(maxsize=None)
def CR(widths, s):
    """Parameter-space codim of {rank(product of layers of these widths) <= s}."""
    v = tuple(widths)
    if len(v) == 2:
        v0, v1 = v
        return 0 if s >= min(v0, v1) else (v0 - s) * (v1 - s)
    a, b = v[-2], v[-1]
    best = None
    for r in range(0, min(a, b) + 1):
        inner = 0 if r <= s else CR(v[:-2] + (r,), s)
        val = (a - r) * (b - r) + inner
        best = val if best is None else min(best, val)
    return best

def minAdm(widths):
    return CR(widths, 0)

# ------------------------------------------------- EXACT rlct of matrix product ||FE||^2
def rlct_matprod(m, q, n):
    """rlct(||F E||^2), F: m x q, E: q x n, at FE=0.  = minAdm(m,q,n)/2 (cited 2-layer Aoyagi)."""
    return CR((m, q, n), 0) / 2.0

# ------------------------------------------------------------------ NUMERIC tube-volume
def product_of_layers(Ls):
    Z = Ls[0]
    for L in Ls[1:]:
        Z = np.einsum('nij,njk->nik', Z, L)
    return Z

def tube_rlct(sampler, loss_fn, ts, N=4_000_000, seed=0, reps=1):
    """
    Estimate rlct via vol{loss<=t}~t^lambda.
    sampler(N,rng)->params; loss_fn(params)->array of losses (>=0).
    Returns (lambda_hat, table of (t,P)).  Uses two-point slopes at the smallest ts.
    """
    rng = np.random.default_rng(seed)
    counts = np.zeros(len(ts))
    total = 0
    for _ in range(reps):
        p = sampler(N, rng)
        f = loss_fn(p)
        total += len(f)
        for i, t in enumerate(ts):
            counts[i] += (f <= t).sum()
    P = counts / total
    m = P > 0
    ts_a = np.array(ts)
    if m.sum() >= 2:
        lam = np.polyfit(np.log(ts_a[m]), np.log(P[m]), 1)[0]
    else:
        lam = float('nan')
    # also the finest two-point slope (least biased by the log^{m-1} factor at small t)
    idx = np.where(m)[0]
    fine = float('nan')
    if len(idx) >= 2:
        i1, i2 = idx[-2], idx[-1]
        fine = (np.log(P[i2]) - np.log(P[i1])) / (np.log(ts_a[i2]) - np.log(ts_a[i1]))
    return lam, fine, list(zip(ts, P))

# ----------------------------------------------------------------- samplers / losses
def box_sampler(shapes, box=1.0):
    def s(N, rng):
        return [rng.uniform(-box, box, size=(N,) + sh) for sh in shapes]
    return s

def dln_loss(widths, box=1.0):
    """full DLN loss ||product||^2 sampled in a small box (near the deep origin)."""
    shapes = [(widths[i], widths[i+1]) for i in range(len(widths) - 1)]
    smp = box_sampler(shapes, box)
    def loss(Ls):
        Z = product_of_layers(Ls)
        return (Z ** 2).sum(axis=(1, 2))
    return smp, loss
