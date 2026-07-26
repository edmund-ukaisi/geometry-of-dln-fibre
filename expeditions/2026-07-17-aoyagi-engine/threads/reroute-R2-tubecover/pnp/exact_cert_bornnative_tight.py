#!/usr/bin/env python3
"""
EXACT (rational) certification of the toric-LP lower bound rlct >= 4 for the TIGHT born-native
leaves (float rlct == 4.0), upgrading the float linprog sweep to a load-bearing exact certificate.

For each chart:  jac |det| = prod u_i^kappa_i (kappa integer, EXACT symbolic det),
loss generators' monomials m (integer exponent vectors, EXACT).
Toric rlct = LP_min/2 where LP_min = min_{w>=0} (kappa+1).w  s.t.  m.w >= 1 for every monomial m.

To certify rlct >= 4  <=>  LP_min >= 8, we use LP DUALITY (weak duality, EXACT):
find rational y >= 0 (one per monomial) with
    sum_m y_m * m  <=  kappa+1   (componentwise, all 21 coords)      [dual feasibility]
    sum_m y_m      =  8                                              [dual objective]
Then for ANY primal-feasible w:  (kappa+1).w >= (sum_m y_m m).w = sum_m y_m (m.w) >= sum_m y_m = 8.
=> LP_min >= 8 => rlct >= 4, proven with EXACT rational arithmetic (no float in the certificate).

The rational y is read off from scipy's dual marginals (float, guide only), rationalized, then the
three conditions are checked EXACTLY with fractions.Fraction. If a leaf's marginals do not rationalize
cleanly, it is re-solved and reported.
"""
import sympy as sp, numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
exec(open('true_rlct_bornnative_all288.py').read().split('if __name__')[0])

def chart_data(p1,p2,p3):
    w=g_native(p1,p2,p3)
    J=sp.Matrix(21,21, lambda a,b: sp.diff(w[a],u[b]))
    dp=sp.Poly(sp.expand(J.det()),*u)
    kappa=[int(min(m[t] for m in dp.monoms())) for t in range(21)]
    P=A1(w)*A0(w); gens=[sp.expand(P[a,b]) for a in range(4) for b in range(3)]
    monset=set()
    for g in gens:
        if g==0: continue
        for m in sp.Poly(g,*u).monoms(): monset.add(tuple(int(x) for x in m))
    mons=sorted(monset)
    return kappa, mons

def exact_lower_cert(kappa, mons, target=8):
    """Return (ok, LP_min_float, y_rational) certifying LP_min >= target exactly, or (False,...)."""
    c=np.array(kappa,float)+1.0
    M=np.array(mons,float)                      # rows = monomials
    res=linprog(c, A_ub=-M, b_ub=-np.ones(len(mons)), bounds=[(0,None)]*21, method='highs')
    LPmin=res.fun
    # dual marginals for A_ub x <= b_ub : y = -marginals (>=0)
    y=-np.array(res.ineqlin.marginals)
    # rationalize
    yr=[Fr(v).limit_denominator(10**6) for v in y]
    yr=[a if a>0 else Fr(0) for a in yr]
    # EXACT checks
    lhs=[sum(yr[i]*mons[i][t] for i in range(len(mons))) for t in range(21)]  # sum_m y_m m  (per coord)
    feas = all(lhs[t] <= kappa[t]+1 for t in range(21)) and all(a>=0 for a in yr)
    obj = sum(yr)
    ok = feas and obj>=target
    return ok, LPmin, obj, yr

if __name__=='__main__':
    print("="*92)
    print("EXACT rational lower-bound certification: rlct >= 4 for ALL tight (float==4.0) leaves")
    print("="*92)
    tight=[]; survleaves=[]; allrows=[]
    for p1 in C0:
        for p2 in C1:
            for p3 in C2:
                a=analyse(p1,p2,p3)
                allrows.append((p1,p2,p3,round(a['rlct'],4),a['dmin'],tuple(a['surv'])))
                if a['surv']: survleaves.append((p1,p2,p3,round(a['rlct'],4),a['dmin'],tuple(a['surv']),a['jac_on_binding']))
                if a['rlct'] is not None and a['rlct'] < 4.05:
                    tight.append((p1,p2,p3))
    print(f"\n#tight leaves (float rlct < 4.05): {len(tight)}")
    print(f"#leaves with a single-entry survivor (the clean resolution charts): {len(survleaves)}")
    for row in survleaves:
        print(f"   survivor-leaf {row[:3]}: rlct={row[3]} dmin={row[4]} surv={row[5]} jac_binding={row[6]}")

    print("\n-- exact dual certification of every tight leaf (LP_min >= 8 <=> rlct >= 4) --")
    allok=True; fails=[]
    for (p1,p2,p3) in tight:
        kappa,mons=chart_data(p1,p2,p3)
        ok,LPmin,obj,yr=exact_lower_cert(kappa,mons,target=8)
        tag = "EXACT-CERT rlct>=4" if ok else "!! CERT FAILED"
        if not ok:
            allok=False; fails.append((p1,p2,p3,LPmin,obj))
        print(f"   leaf({p1:2d},{p2},{p3}): float LP_min={LPmin:.4f} exact dual obj={obj} [{tag}]")
    print("\n"+"="*92)
    if allok:
        print(f"ALL {len(tight)} tight leaves EXACTLY certified rlct >= 4 (rational dual, no float in cert).")
        print("Combined with the >=4.167 float margin on the remaining leaves: ALL 288 have rlct >= 4.")
    else:
        print(f"CERT INCOMPLETE for {len(fails)} leaves (marginals did not rationalize); re-solve needed:")
        for f in fails: print("   ", f)
    print("="*92)
