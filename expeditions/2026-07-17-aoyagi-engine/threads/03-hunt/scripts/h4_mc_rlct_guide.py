#!/usr/bin/env python3
"""HUNT h4 -- Monte-Carlo RLCT estimate (GUIDE ONLY, float; decorrelated from the
blow-up construction). NOT a certificate: it can only FLAG a suspected value error
to pursue exactly; a consistent estimate corroborates but never proves.

Volume scaling: V(t)=Vol{C in box: F(C)<t} ~ const t^{rlct} (-log t)^{theta-1}, so
local slope d log V / d log t -> rlct. Estimate V(t) by uniform MC (numpy-vectorized)
on a box at a geometric ladder of t; read the slope where counts are still large.
Compare to 1/2 minAdm: slope clearly below => suspected value kill (chase exactly).
"""
import sys, math
import numpy as np
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm


def F_batch(M, X):
    """X: (nsamp, N) float array of entries. Returns F = ||prod C||^2 per sample."""
    L = len(M) - 1
    n = X.shape[0]
    off = 0
    mats = []
    for s in range(1, L + 1):
        r, c = M[s - 1], M[s]
        mats.append(X[:, off:off + r * c].reshape(n, r, c))
        off += r * c
    P = mats[0]
    for m in mats[1:]:
        P = np.matmul(P, m)   # batched matmul
    return (P ** 2).sum(axis=(1, 2))


def estimate(M, half_width=1.0, nsamp=2_000_000, batch=500_000, kmax=30, seed=1):
    L = len(M) - 1
    N = sum(M[s - 1] * M[s] for s in range(1, L + 1))
    rng = np.random.default_rng(seed)
    ladder = np.array([2.0 ** (-k) for k in range(kmax)])
    counts = np.zeros(kmax, dtype=np.int64)
    done = 0
    while done < nsamp:
        b = min(batch, nsamp - done)
        X = rng.uniform(-half_width, half_width, size=(b, N))
        f = F_batch(M, X)
        # counts[i] = #{f < ladder[i]}
        counts += (f[:, None] < ladder[None, :]).sum(axis=0)
        done += b
    slopes = []
    for i in range(kmax - 1):
        c1, c2 = counts[i], counts[i + 1]
        if c1 >= 300 and c2 >= 300:
            s = math.log(c1 / c2) / math.log(ladder[i] / ladder[i + 1])
            slopes.append((ladder[i], s, int(c1), int(c2)))
    return counts, slopes


if __name__ == "__main__":
    from fractions import Fraction as Fr
    instances = [(2, 2, 2), (2, 2, 3), (3, 3, 4), (2, 2, 2, 2), (2, 3, 2, 2), (4, 4, 4, 4)]
    nsamp = int(sys.argv[1]) if len(sys.argv) > 1 else 4_000_000
    for M in instances:
        ma = minAdm(M); half = Fr(ma, 2)
        _, slopes = estimate(M, nsamp=nsamp, seed=2024)
        tail = slopes[-7:] if len(slopes) >= 7 else slopes
        print(f"M={M}: 1/2 minAdm={half}={float(half):.3f}  (rlct est should settle near this)")
        for (t, s, c1, c2) in tail:
            flag = "  <== BELOW" if s < float(half) - 0.3 else ""
            print(f"   t~{t:.1e}: slope={s:.3f}  (counts {c1}->{c2}){flag}")
        print()
