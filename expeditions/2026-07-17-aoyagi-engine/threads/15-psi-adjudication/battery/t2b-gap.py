#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/15-psi-adjudication (pnp-psi). T2(b): at the smallest node where the ACTUAL
#   Aoyagi gauge bites (2x2 d-block + u divisor, d_center=5), does the PER-EDGE-psi family
#   (u-pivot psi=id, d-pivots psi=Schur) still image-cover the cube, or does it open a GAP?
#   Compare to the PURE-beta family (R-b, no psi) which tiles exactly (Leg 1).
# Exact rational grid. NO Monte-Carlo. This prices R-a (per-edge psi) vs R-b (source-reparam).
from fractions import Fraction as F
from itertools import product
import sys

# center coords: index 0=d11, 1=d12, 2=d21, 3=d22, 4=u.  (2x2 d-block + divisor u)
D11,D12,D21,D22,U = 0,1,2,3,4
NC = 5

def is_max(i, x):
    """coord i is a max-modulus coord of x (with pivot-0 forces all 0)."""
    if x[i] == 0:
        return all(v == 0 for v in x)
    return all(abs(x[k]) <= abs(x[i]) for k in range(NC))

# per-edge gauge psi_e on the ambient center coords (Schur residual update; ratios fixed).
# residual entry (i,j) for pivot (r,c):  d_ij -> d_ij - d_ic*d_rj/d_rc.  (2x2: single residual)
def psi(e, x):
    x = list(x)
    if e == U:                         # Case-1(1): u-pivot carries NO gauge
        return tuple(x)
    if e == D11 and x[D11] != 0:       # pivot(0,0); residual d22 -> d22 - d21*d12/d11
        x[D22] = x[D22] - x[D21]*x[D12]/x[D11]
    elif e == D12 and x[D12] != 0:     # pivot(0,1); residual d21 -> d21 - d22*d11/d12
        x[D21] = x[D21] - x[D22]*x[D11]/x[D12]
    elif e == D21 and x[D21] != 0:     # pivot(1,0); residual d12 -> d12 - d11*d22/d21
        x[D12] = x[D12] - x[D11]*x[D22]/x[D21]
    elif e == D22 and x[D22] != 0:     # pivot(1,1); residual d11 -> d11 - d12*d21/d22
        x[D11] = x[D11] - x[D12]*x[D21]/x[D22]
    return tuple(x)

def psi_inv(e, p):
    """inverse gauge: same shear with + sign (unipotent involution structure per-coordinate)."""
    p = list(p)
    if e == U:
        return tuple(p)
    if e == D11 and p[D11] != 0:
        p[D22] = p[D22] + p[D21]*p[D12]/p[D11]
    elif e == D12 and p[D12] != 0:
        p[D21] = p[D21] + p[D22]*p[D11]/p[D12]
    elif e == D21 and p[D21] != 0:
        p[D12] = p[D12] + p[D11]*p[D22]/p[D21]
    elif e == D22 and p[D22] != 0:
        p[D11] = p[D11] + p[D12]*p[D21]/p[D22]
    return tuple(p)

def covered_pure(p):
    """PURE-beta family (R-b): p covered iff some coord is max-modulus (tiling)."""
    return any(is_max(e, p) for e in range(NC))

def covered_peredge(p):
    """PER-EDGE-psi family (R-a): p in union_e psi_e(sector_e) iff psi_e^{-1}(p) is e-max."""
    return any(is_max(e, psi_inv(e, p)) for e in range(NC))

def run(steps=4, R=1):
    vals = [F(-R) + F(2*R, steps)*s for s in range(steps+1)]
    pure_miss = []
    peredge_gap = []          # covered by pure, NOT by per-edge -> the gap
    for p in product(vals, repeat=NC):
        cp = covered_pure(p)
        ce = covered_peredge(p)
        if not cp:
            pure_miss.append(p)
        if cp and not ce:
            peredge_gap.append(p)
    return pure_miss, peredge_gap

if __name__ == "__main__":
    print("T2(b) — per-edge-psi cover gap at the 2x2+u node (d_center=5), exact rational grid")
    pure_miss, gap = run(steps=4)
    print(f"  PURE-beta family (R-b) misses: {len(pure_miss)} cube points (expect 0 -> tiles)")
    print(f"  PER-EDGE-psi family (R-a) GAP (pure-covered but psi-missed): {len(gap)} points")
    if gap:
        g = gap[0]
        print(f"  witness gap point p = {[str(v) for v in g]}")
        # show WHY: which coord is max (pure covers via that d-pivot), and psi displaced it out
        maxc = [e for e in range(NC) if is_max(e, g)]
        print(f"    pure-cover pivot(s): {maxc};  per-edge coverage per edge:",
              {e: is_max(e, psi_inv(e, g)) for e in range(NC)})
    ok = (len(pure_miss) == 0) and (len(gap) > 0)
    print()
    print("VERDICT T2(b):", "PASS -- pure-beta tiles; per-edge-psi OPENS A REAL GAP" if ok
          else ("NO GAP FOUND (per-edge covers)" if len(pure_miss)==0 else "PURE MISSED?!"))
    sys.exit(0 if ok else 1)
