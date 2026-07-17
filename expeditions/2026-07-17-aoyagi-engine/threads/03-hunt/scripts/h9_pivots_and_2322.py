#!/usr/bin/env python3
"""HUNT h9 -- adversarial extras:
  (B2) alternative pivot: (3,3,4) incidence at pivot (1,1) and (2,2) -- ratio must be
       pivot-independent (permutation invariance of the divisor ratios).
  (L=3 cross-check) (2,3,2,2) double incidence chart (C1 2x3, C2 3x2) + LP.
  (B4) independentize sanity: show the ACTUAL (3,3,4) t=(1,0) chart ideal is NOT the
       'independentised' ideal that would give the spurious 3 -- the genuine chart gives 4.
"""
import sys
import sympy as sp
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/threads/03-hunt/scripts")
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm
from h7_chart_lp import min_ratio_exact, min_ratio_lp


def build_L2_chart_pivot(M0, M1, M2, piv=(0, 0)):
    p, q = piv
    al = sp.Symbol("al")
    a = {j: sp.Symbol(f"a{j}") for j in range(M1) if j != q}
    b = {i: sp.Symbol(f"b{i}") for i in range(M0) if i != p}
    D = {(i, j): sp.Symbol(f"D{i}_{j}") for i in range(M0) for j in range(M1) if i != p and j != q}
    C1 = sp.zeros(M0, M1)
    for i in range(M0):
        for j in range(M1):
            if i == p and j == q:
                C1[i, j] = al
            elif i == p:
                C1[i, j] = al * a[j]
            elif j == q:
                C1[i, j] = al * b[i]
            else:
                C1[i, j] = al * (b[i] * a[j] + D[(i, j)])
    # shear C2 exposing the pivot-row contraction g = row p + sum_{j!=q} a_j row j
    c = {(i, k): sp.Symbol(f"c{i}_{k}") for i in range(M1) for k in range(M2) if i != p}
    g = [sp.Symbol(f"g{k}") for k in range(M2)]
    C2 = sp.zeros(M1, M2)
    for k in range(M2):
        C2[p, k] = g[k] - sum(a[j] * c[(j, k)] for j in range(M1) if j != q)
    for i in range(M1):
        if i == p:
            continue
        for k in range(M2):
            C2[i, k] = c[(i, k)]
    newvars = [al] + [a[j] for j in sorted(a)] + [b[i] for i in sorted(b)] \
              + [D[k] for k in sorted(D)] + g + [c[k] for k in sorted(c)]
    old = [C1[i, j] for i in range(M0) for j in range(M1)] + \
          [C2[i, k] for i in range(M1) for k in range(M2)]
    Jdet = sp.expand(sp.Matrix([[sp.diff(e, v) for v in newvars] for e in old]).det())
    P = sp.expand(C1 * C2)
    gens = [sp.expand(P[i, j]) for i in range(M0) for j in range(M2)]

    def sup(e):
        e = sp.expand(e)
        return [] if e == 0 else [tuple(int(x) for x in m) for m in sp.Poly(e, *newvars).monoms()]
    return newvars, [sup(gm) for gm in gens if gm != 0], sup(Jdet), Jdet


def build_2322():
    """M=(2,3,2,2): C1 2x3 incidence (pivot 0,0), C2 3x2 incidence (pivot 0,0), C3 2x2 free."""
    al1, a11, a12, b11, D111, D112 = sp.symbols("al1 a11 a12 b11 D111 D112")
    C1 = sp.Matrix([[al1, al1 * a11, al1 * a12],
                    [al1 * b11, al1 * (b11 * a11 + D111), al1 * (b11 * a12 + D112)]])  # 2x3
    al2, a21, b21, b22, D211, D221 = sp.symbols("al2 a21 b21 b22 D211 D221")
    C2 = sp.Matrix([[al2, al2 * a21],
                    [al2 * b21, al2 * (b21 * a21 + D211)],
                    [al2 * b22, al2 * (b22 * a21 + D221)]])  # 3x2
    p, q, r, s = sp.symbols("p q r s")
    C3 = sp.Matrix([[p, q], [r, s]])
    newvars = [al1, a11, a12, b11, D111, D112, al2, a21, b21, b22, D211, D221, p, q, r, s]
    old = [C1[i, j] for i in range(2) for j in range(3)] + \
          [C2[i, j] for i in range(3) for j in range(2)] + \
          [C3[i, j] for i in range(2) for j in range(2)]
    Jdet = sp.expand(sp.Matrix([[sp.diff(e, v) for v in newvars] for e in old]).det())
    P = sp.expand(C1 * C2 * C3)
    gens = [sp.expand(P[i, j]) for i in range(2) for j in range(2)]

    def sup(e):
        e = sp.expand(e)
        return [] if e == 0 else [tuple(int(x) for x in m) for m in sp.Poly(e, *newvars).monoms()]
    return newvars, [sup(gm) for gm in gens if gm != 0], sup(Jdet), Jdet


if __name__ == "__main__":
    print("=== (B2) alternative-pivot invariance: (3,3,4) ===")
    for piv in [(0, 0), (1, 1), (2, 2)]:
        nv, gs, js, Jd = build_L2_chart_pivot(3, 3, 4, piv)
        val, _ = min_ratio_lp(gs, js, len(nv))
        print(f"   pivot {piv}: Jac={Jd}, LP min 2rho={val:.4f} (rho={val/2:.4f})  "
              f"-> {'SURVIVE' if val >= 8 - 1e-6 else 'KILL'}")

    print("\n=== (L=3 cross-check) (2,3,2,2) double-incidence chart ===")
    nv, gs, js, Jd = build_2322()
    ma = minAdm((2, 3, 2, 2))
    val, x = min_ratio_lp(gs, js, len(nv))
    print(f"   #newvars={len(nv)}, Jac={Jd}, minAdm={ma} (target 2rho={ma})")
    print(f"   LP min 2rho={val:.6f} (rho={val/2:.6f})  -> {'SURVIVE' if val >= ma - 1e-6 else 'KILL'}")
