#!/usr/bin/env python3
"""D2 non-deepest reduction census (EXACT).

At a non-deepest point of the homogeneous core F = ||prod_s C^{(s)}||^2, block
elimination (Aoyagi Lemma 2 = a UNIT change of variables, RLCT-preserving by
Lemma 1) using a rank-t_1 regular pivot in layer 1 splits (for L=2, disjoint vars):

    F  ~   ||(top t_1 rows)||^2            [chain (t_1, M2)  -- the regular block]
         + ||C_4 . (bottom M1-t_1 rows)||^2 [chain (M0-t_1, M1-t_1, M2) -- residual core]

so   rlct_w  =  1/2 * minAdm(t_1, M2)  +  1/2 * minAdm(M0-t_1, M1-t_1, M2)
            =  1/2 * [ nReg + minAdm(M') ]          (nReg = t_1*M2 = minAdm(t_1,M2)).

The dissolve claim (theorem4-localization, amended form): each such stratum is an
EXACT CoV to strictly-smaller arity, and the threshold is PRESERVED, i.e.

    nReg + minAdm(M')  >=  minAdm(M)          [MinAdmMono / minAdm-as-minimum]

so  rlct_w >= 1/2 minAdm(M) = rlct_0  (the deepest point is the worst) -- WITHOUT
using rlct = c* (circularity guard): this is a pure minAdm arithmetic fact.

We CERTIFY rlct_w two ways for L=2: (a) the Newton-LP on the reduced monomial
ideal, (b) the closed-form 1/2[nReg + minAdm(M')]. They must agree, AND every
stratum must satisfy the compensation inequality.
"""
import sys
from fractions import Fraction as F
sys.path.insert(0, "/tmp")
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from rlct_newton import rlct_monomial_ideal, rlct_monomial_ideal_lp
from _minadm import minAdm


def reduced_ideal_L2(M0, M1, M2, t1):
    """Monomial ideal of the block-eliminated (M0,M1,M2) core at a rank-t1 layer-1 pivot.
    Vars: top block entries (t1 x M2), C_4 entries ((M0-t1) x (M1-t1)),
          bottom rows of C2' ((M1-t1) x M2).
    Generators:
      top:    each of the t1*M2 entries of the top rows -> a coordinate (regular).
      bottom: C_4[a,b] * c2bot[b,j]  for a in M0-t1, b in M1-t1, j in M2.
    """
    top = t1 * M2
    r = M0 - t1          # residual rows
    c = M1 - t1          # residual cols
    nC4 = r * c
    nbot = c * M2
    nvars = top + nC4 + nbot
    gens = []
    # top regular coordinates
    for i in range(top):
        e = [0] * nvars
        e[i] = 1
        gens.append(tuple(e))
    # bottom coupled generators C_4[a,b]*c2bot[b,j]
    def C4(a, b): return top + a * c + b
    def cbot(b, j): return top + nC4 + b * M2 + j
    for a in range(r):
        for b in range(c):
            for j in range(M2):
                e = [0] * nvars
                e[C4(a, b)] += 1
                e[cbot(b, j)] += 1
                gens.append(tuple(e))
    return gens, nvars, top


def census(M):
    M0, M1, M2 = M
    print(f"\n=== chain {M}:  minAdm = {minAdm(M)},  rlct_0 = {F(minAdm(M),2)} ===")
    print(f"  {'t1':>3} {'nReg=minAdm(t1,M2)':>18} {'M_residual':>14} {'minAdm(M_res)':>13} "
          f"{'nReg+minAdm(M_res)':>18} {'rlct_w (NewtonLP)':>17} {'>=rlct_0?':>9}")
    ok = True
    r0 = F(minAdm(M), 2)
    for t1 in range(1, min(M0, M1) + 1):   # non-deepest: t1>=1 (some layer-1 pivot regular)
        Mres = (M0 - t1, M1 - t1, M2)
        nReg = minAdm((t1, M2))            # = t1*M2
        comp = nReg + minAdm(Mres)
        gens, nv, top = reduced_ideal_L2(M0, M1, M2, t1)
        rlct_cf = F(comp, 2)               # closed form 1/2[nReg+minAdm(Mres)]  -- EXACT certificate
        if nv <= 9:
            rlct_check = rlct_monomial_ideal(gens, nv)      # exact vertex enum
            agree = (rlct_check == rlct_cf); mode = "exact"
        else:
            fv = rlct_monomial_ideal_lp(gens, nv)           # float guide
            agree = (fv is not None and abs(fv - float(rlct_cf)) < 1e-9); mode = "float"
            rlct_check = rlct_cf
        dom = (rlct_cf >= r0)
        compok = (comp >= minAdm(M))
        ok &= agree and dom and compok
        flag = "OK" if (agree and dom and compok) else "FAIL"
        print(f"  {t1:>3} {nReg:>18} {str(Mres):>14} {minAdm(Mres):>13} "
              f"{comp:>18} {str(rlct_cf):>17} {str(dom):>9}  [LP==CF:{agree}/{mode}] {flag}")
    return ok


if __name__ == "__main__":
    allok = True
    for M in [(2, 2, 2), (2, 2, 3), (3, 3, 4), (3, 2, 3)]:
        allok &= census(M)
    print("\nALL PASS" if allok else "\nSOME FAILED")
    sys.exit(0 if allok else 1)
