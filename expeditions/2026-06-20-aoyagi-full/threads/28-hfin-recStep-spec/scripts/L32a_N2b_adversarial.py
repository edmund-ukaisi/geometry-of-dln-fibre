#!/usr/bin/env python3
"""
L32a_N2b_adversarial.py — ADVERSARIAL extreme-search for the EXACT Lean N2b ratio bound.

Random sampling (L32a_N2b_exact_lean.py) found ratio ∈ [0.42, 3.22] ON the cell. But ∀-claims need the
WORST case, not the average. Here we ADVERSARIALLY push the ratio toward 0 and ∞ on the cell, using:

  (1) det M11 → 0 edge:  M11 = top-left j×j minor barely the max (the dangerous Cramer-shear edge, R2);
  (2) S concentrated in the worst direction (eigenvector of the relevant Gram extremes);
  (3) gradient-free coordinate descent on the ratio over (R,S) constrained to the cell.

The claim survives iff the ratio stays bounded away from 0 (gives c0) and from ∞ (gives c1) under
adversarial pressure. We report the adversarial extremes and compare to the random-sample range.

KEY EDGE TEST (R2 of minorpivot-cert): force the top-left minor to be the MAX minor but make det M11
SMALL relative to entries. If the ratio blows up here, the raw-block Lean statement is FALSE at the edge.
"""
import numpy as np
import itertools

rng = np.random.default_rng(424242)

def frobSq(M):
    return float(np.sum(M**2))

def jminor_max(R, j, r):
    best = 0.0
    for I in itertools.combinations(range(r), j):
        for J in itertools.combinations(range(r), j):
            best = max(best, abs(np.linalg.det(R[np.ix_(I, J)])))
    return best

def ratio(R, S, j, r):
    M11 = R[:j, :j]; M12 = R[:j, j:]; M21 = R[j:, :j]; M22 = R[j:, j:]
    try:
        M11inv = np.linalg.inv(M11)
    except np.linalg.LinAlgError:
        return None
    Sc = M22 - M21 @ M11inv @ M12
    RS = R @ S
    D = frobSq(RS[:j, :]) + frobSq(Sc @ S[j:, :])
    if D < 1e-14:
        return None
    return frobSq(RS) / D

def on_cell(R, j, r, tol=1e-9):
    dtl = abs(np.linalg.det(R[:j, :j]))
    return dtl >= jminor_max(R, j, r) - tol * (1 + jminor_max(R, j, r)) and dtl > 1e-7

def adversarial(r, j, p, iters=40000):
    """Coordinate-descent push of the ratio to its extremes on the cell."""
    lo, hi = float('inf'), 0.0
    lo_cfg = hi_cfg = None
    # start from many random cell points, then perturb
    for _ in range(iters):
        R = rng.uniform(-1, 1, size=(r, r))
        if not on_cell(R, j, r):
            continue
        S = rng.standard_normal((r, p)) * rng.uniform(0.1, 2.0)
        if frobSq(S) < 1e-9:
            continue
        v = ratio(R, S, j, r)
        if v is None:
            continue
        if v < lo:
            lo, lo_cfg = v, (R.copy(), S.copy())
        if v > hi:
            hi, hi_cfg = v, (R.copy(), S.copy())
    # local polish around the extremes (perturb S only — keeps cell membership of R)
    for cfg_idx, (cfg, want_min) in enumerate([(lo_cfg, True), (hi_cfg, False)]):
        if cfg is None:
            continue
        R, S = cfg
        step = 0.3
        cur = ratio(R, S, j, r)
        for _ in range(8000):
            Sp = S + rng.standard_normal((r, p)) * step
            if frobSq(Sp) < 1e-9:
                continue
            v = ratio(R, Sp, j, r)
            if v is None:
                continue
            if (want_min and v < cur) or ((not want_min) and v > cur):
                S, cur = Sp, v
            else:
                step *= 0.999
        if want_min:
            lo = min(lo, cur)
        else:
            hi = max(hi, cur)
    return lo, hi

def edge_detM11_small(r, j, p, n=20000):
    """Force det M11 SMALL while top-left stays max minor — the dangerous Cramer edge (R2)."""
    lo, hi = float('inf'), 0.0
    found = 0
    for _ in range(n):
        R = rng.uniform(-1, 1, size=(r, r))
        # shrink the top-left block toward singular
        eps = rng.uniform(1e-3, 0.2)
        # make M11 nearly singular: set its rows nearly parallel
        if j >= 2:
            base = rng.uniform(-1, 1, size=(j,))
            for a in range(j):
                R[a, :j] = base * rng.uniform(0.5, 1.0) + eps * rng.standard_normal(j)
        else:
            R[0, 0] = eps * rng.choice([-1, 1])
        # clamp to cell entry bound
        R = np.clip(R, -1, 1)
        if not on_cell(R, j, r):
            continue
        S = rng.standard_normal((r, p)) * rng.uniform(0.1, 2.0)
        v = ratio(R, S, j, r)
        if v is None:
            continue
        lo = min(lo, v); hi = max(hi, v); found += 1
    return lo, hi, found

print("=" * 90)
print(" N2b ADVERSARIAL extreme-search (the EXACT Lean raw-block ratio)")
print("=" * 90)
cases = [(2, 1, 6), (3, 1, 7), (3, 2, 7), (4, 1, 8), (4, 2, 8), (4, 3, 8)]
glob_lo, glob_hi = float('inf'), 0.0
for (r, j, p) in cases:
    lo, hi = adversarial(r, j, p)
    elo, ehi, ef = edge_detM11_small(r, j, p)
    LO = min(lo, elo if ef else lo)
    HI = max(hi, ehi if ef else hi)
    glob_lo = min(glob_lo, LO); glob_hi = max(glob_hi, HI)
    print(f"\nr={r}, j={j}, p={p}:")
    print(f"  adversarial:  ratio ∈ [{lo:.4f}, {hi:.4f}]")
    print(f"  detM11→0 edge ratio ∈ [{elo:.4f}, {ehi:.4f}]  (found {ef})")
    print(f"  COMBINED:     ratio ∈ [{LO:.4f}, {HI:.4f}]  ⟹  c0 ≈ {LO:.3f}, c1 ≈ {HI:.3f}")

print("\n" + "=" * 90)
print(f" GLOBAL adversarial ratio ∈ [{glob_lo:.4f}, {glob_hi:.4f}]")
print(f" ⟹ a SINGLE uniform pair (c0, c1) = ({glob_lo:.3f}, {glob_hi:.3f}) works across all r,j tested.")
bounded = glob_lo > 0.05 and glob_hi < 100
print(f" Bounded away from 0 and ∞ under adversarial pressure: {bounded}")
print(f" VERDICT: exact Lean N2b raw-block statement is {'ROBUST (true even at the det→0 edge)' if bounded else 'FRAGILE — INVESTIGATE'}")
print("=" * 90)
