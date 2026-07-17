#!/usr/bin/env python3
"""HUNT h8 -- general L=2 incidence(C1, rank-1 pivot) + shear(C2) chart + exact/LP min ratio.

C1 (M0xM1) incidence at pivot (0,0):  alpha; a_j (row0), b_i (col0), Delta_ij (residual);
  C1[0][0]=al, C1[0][j]=al a_j, C1[i][0]=al b_i, C1[i][j]=al(b_i a_j + D_ij).
  Jacobian(C1) = al^(M0*M1 - 1).
C2 (M1xM2) shear exposing the first-row contraction g = [1,a]. C2:  row0 entries replaced
  by g_k, i.e. C2[0][k] = g_k - sum_{j>=1} a_j C2[j][k]; rows>=1 free. Jacobian(shear)=1.

For M=(3,3,4) a single rank-1 peel leaves a 2x2 Delta-block -> the corank-2 sharing
regime the D3 cert flags. We compute the EXACT (or LP) min ratio over the chart and
check no undershoot below minAdm. Genuine chart => any undershoot is a real value kill.
"""
import sys
import sympy as sp
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/threads/03-hunt/scripts")
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm
from h7_chart_lp import min_ratio_exact, min_ratio_lp


def build_L2_chart(M0, M1, M2):
    al = sp.Symbol("al")
    a = [sp.Symbol(f"a{j}") for j in range(1, M1)]          # M1-1
    b = [sp.Symbol(f"b{i}") for i in range(1, M0)]          # M0-1
    D = {(i, j): sp.Symbol(f"D{i}_{j}") for i in range(1, M0) for j in range(1, M1)}
    # C1 in incidence coords
    C1 = sp.zeros(M0, M1)
    C1[0, 0] = al
    for j in range(1, M1):
        C1[0, j] = al * a[j - 1]
    for i in range(1, M0):
        C1[i, 0] = al * b[i - 1]
    for i in range(1, M0):
        for j in range(1, M1):
            C1[i, j] = al * (b[i - 1] * a[j - 1] + D[(i, j)])
    # C2: rows>=1 free coords c_{i,k}; row0 sheared to g_k
    c = {(i, k): sp.Symbol(f"c{i}_{k}") for i in range(1, M1) for k in range(M2)}
    g = [sp.Symbol(f"g{k}") for k in range(M2)]
    C2 = sp.zeros(M1, M2)
    for k in range(M2):
        C2[0, k] = g[k] - sum(a[j - 1] * c[(j, k)] for j in range(1, M1))
    for i in range(1, M1):
        for k in range(M2):
            C2[i, k] = c[(i, k)]
    newvars = [al] + a + b + [D[k] for k in sorted(D)] + g + [c[k] for k in sorted(c)]
    # old entries
    old = [C1[i, j] for i in range(M0) for j in range(M1)] + \
          [C2[i, k] for i in range(M1) for k in range(M2)]
    Jdet = sp.expand(sp.Matrix([[sp.diff(e, v) for v in newvars] for e in old]).det())
    P = sp.expand(C1 * C2)
    gens = [sp.expand(P[i, j]) for i in range(M0) for j in range(M2)]

    def support(expr):
        expr = sp.expand(expr)
        if expr == 0:
            return []
        return [tuple(int(e) for e in m) for m in sp.Poly(expr, *newvars).monoms()]
    gen_sup = [support(gm) for gm in gens if gm != 0]
    jac_sup = support(Jdet)
    return newvars, gen_sup, jac_sup, Jdet


if __name__ == "__main__":
    for M in [(2, 2, 2), (2, 2, 3), (3, 3, 4)]:
        M0, M1, M2 = M
        newvars, gen_sup, jac_sup, Jdet = build_L2_chart(M0, M1, M2)
        nv = len(newvars)
        ma = minAdm(M)
        print(f"=== M={M}: #newvars={nv}, Jac={Jdet}, minAdm={ma} (target 2rho={ma}) ===")
        if nv <= 9 and sum(len(s) for s in gen_sup) + nv <= 20:
            best, _ = min_ratio_exact(gen_sup, jac_sup, nv)
            print(f"   EXACT vertex-enum min 2rho={best} (rho={best/2})  "
                  f"-> {'SURVIVE' if best >= ma else 'KILL'}")
        else:
            val, x = min_ratio_lp(gen_sup, jac_sup, nv)
            surv = val is not None and val >= ma - 1e-6
            print(f"   LP min 2rho={val:.6f} (rho={val/2:.6f})  -> {'SURVIVE' if surv else 'KILL'}")
