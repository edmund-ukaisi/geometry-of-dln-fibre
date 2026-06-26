#!/usr/bin/env python3
"""
[SUPERSEDED by n2b_shear_and_ratio.py — kept for provenance. The rejection sampling for
 max-modulus minors here is slow; n2b_shear_and_ratio.py builds cells efficiently and adds the
 exact full-cancellation worst case. The exact verdict is in n2b_exact_cancellation.py.]

N2b LOWER-direction test (the only direction hfin needs).

hfin needs:  F^{-c'} integrable.  If  c0 * D <= F  with c0>0 UNIFORM on the bounded
complete-pivoting cell, then  F^{-c'} <= c0^{-c'} * D^{-c'}, so D-integrability => F-integrability.

Here:
   F = frobSq(R*S)                       (the binding corank-r core)
   D = frobSq((R*S)_top) + frobSq(Sc*S_bot)   (the disjoint Morse-top + Schur-bottom split)
where for a j-pivot:
   (R*S)_top  = top j rows of R*S
   Sc         = M22 - M21*M11^{-1}*M12   (genuine Schur complement, (r-j)x(r-j))
   S_bot      = bottom (r-j) rows of S

The (3,3,4) anchor proved the LOWER bound with c0 = 1/5 on |gamma|<=1 (one-sided, NOT two-sided!).
QUESTION: does the LOWER bound hold UNIFORMLY at corank >= 2 (r>=3, j chosen as max-modulus minor)?

We test by SEARCHING for a counterexample: a bounded-cell (R,S) with F small but D bounded away from 0.
That is: minimize ratio  F / D  over the bounded complete-pivoting cell.  If inf > 0 uniform => lower
bound holds. If inf = 0 (a sequence with F/D -> 0) => NO uniform c0 => lower bound BREAKS.

Exact-algebra strategy: parametrize, compute the ratio symbolically, then probe degeneracies exactly.
MC only as a guide to locate candidate degeneracies; the verdict uses exact rational checks.
"""
import numpy as np
import sympy as sp

np.random.seed(0)

def frobSq(M):
    M = np.atleast_2d(M)
    return float(np.sum(M*M))

def schur_split_ratio(R, S, j):
    """R: r x r, S: r x p, j-pivot top-left block. Returns F, D, ratio with TOP-LEFT pivot."""
    r = R.shape[0]
    RS = R @ S
    F = frobSq(RS)
    top = RS[:j, :]                     # (R*S)_top
    M11 = R[:j, :j]
    M12 = R[:j, j:]
    M21 = R[j:, :j]
    M22 = R[j:, j:]
    Sc = M22 - M21 @ np.linalg.inv(M11) @ M12
    Sbot = S[j:, :]
    D = frobSq(top) + frobSq(Sc @ Sbot)
    return F, D, (F / D if D > 1e-300 else np.inf)

def is_max_modulus_minor(R, j):
    """Check top-left j-minor is a max-modulus j-minor (the complete-pivoting cell)."""
    from itertools import combinations
    r = R.shape[0]
    target = abs(np.linalg.det(R[:j, :j]))
    if target < 1e-14:
        return False, target, 0.0
    mx = 0.0
    for I in combinations(range(r), j):
        for J in combinations(range(r), j):
            d = abs(np.linalg.det(R[np.ix_(I, J)]))
            mx = max(mx, d)
    return (target >= mx - 1e-12), target, mx

print("=" * 70)
print("MC GUIDE: search bounded complete-pivoting cell for small F/D (corank-2)")
print("=" * 70)
# r=3, j=1 (corank-2 residual), p=4. Bounded cell: |R_ab|<=1, top-left 1-minor (=R00) is max modulus.
for (r, j, p, label) in [(3, 1, 4, "r=3,j=1 (corank-2 residual)"),
                          (3, 2, 4, "r=3,j=2 (corank-1 residual)"),
                          (4, 1, 4, "r=4,j=1 (corank-3 residual)"),
                          (4, 2, 4, "r=4,j=2 (corank-2 residual)")]:
    best = np.inf
    best_RS = None
    for _ in range(400000):
        R = np.random.uniform(-1, 1, (r, r))
        # enforce max-modulus: scale so |R00...|... actually just reject if not max-modulus minor
        ok, tgt, mx = is_max_modulus_minor(R, j)
        if not ok:
            continue
        S = np.random.uniform(-1, 1, (r, p))
        F, D, ratio = schur_split_ratio(R, S, j)
        if D > 1e-9 and ratio < best:
            best = ratio
            best_RS = (R.copy(), S.copy())
    print(f"  {label}: inf F/D found ~ {best:.6f}")
