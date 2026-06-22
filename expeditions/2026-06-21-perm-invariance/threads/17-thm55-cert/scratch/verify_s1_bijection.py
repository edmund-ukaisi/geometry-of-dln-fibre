#!/usr/bin/env python3
"""
verify_s1_bijection.py — the S1 shift lemma (paper Lemma 5.7, r=s form):
    Qseries(d-s) 0 = (q)_s * Qseries d s,    (q)_s = prod_{k=1}^s (1-X^k).
This is the q-series LIFT of the LANDED orbit-level rankShift (dropCorner /
kostantEquivShift in CTheta).  We pin its bijective content so the formaliser
knows EXACTLY what to prove on top of the LANDED bijection.

The bijection (paper sec:add_longest): Kostant partitions of (d-s) with corner 0
<-> Kostant partitions of d with corner s, via m'_{0N} = m_{0N} + s (add s to the
all-covering corner [0,N]).  Equivalently dropCorner / Function.update at (0,last).
PROPERTIES under m <-> m' (m corner s of d ; m' = dropCorner m, corner 0 of d-s):
  (a) codimForm preserved:  codim(m) = codim(m')   [LANDED: codimForm_update_corner].
  (b) Pm change:  Pm(m) = Pm(m') * P_s / P_0 = Pm(m') * P_s,  BUT WAIT:
      Pm(m) = prod_{i<=j} P(m_{ij}); the only differing entry is the corner (0,N):
      m_{0N}=s vs m'_{0N}=0, so  Pm(m) = Pm(m') * P_s / P_0 = Pm(m') * P_s   (P_0=1).
  So  Qseries d s = sum_{m corner s} X^{codim m} Pm(m)
                  = sum_{m' corner 0 of d-s} X^{codim m'} Pm(m') * P_s
                  = P_s * Qseries(d-s) 0.
  Hence  Qseries d s = P_s * Qseries(d-s) 0,  i.e.  Qseries(d-s) 0 = P_s^{-1} Qseries d s
       = (q)_s Qseries d s    [since (q)_s = P_s^{-1}].
  *** So the CLEAN q-series statement (avoiding (q)_s entirely) is:
        S1':  Qseries d s = P_s * Qseries(d-s) 0.   ***
  This is EXACTLY the form S2 needs (eqn:key:  Pmult d = sum_s P_s Qseries(d-s) 0),
  and it avoids defining (q)_s and proving (q)_s P_s = 1.  Use S1' not S1.

We verify S1' directly:  Qseries_def(d, s) == P_s * Qseries_def(d-s, 0).
And the Pm corner-change (b): for any m corner s, Pm(m) = P_s * Pm(dropCorner m).
"""
import sympy as sp
from verify_s3 import q, P, Qseries_def, DEG, eq_upto, kostant_partitions

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)

if __name__ == '__main__':
    tests = [(2,2,2),(2,3,2),(2,2,3),(2,4,2),(1,2,3),(3,2,1),(3,3,3),(1,2,2,3)]
    print("S1' (the clean form):  Qseries(d, s) == P_s * Qseries(d-s, 0):")
    ok = True
    for d in tests:
        mind = min(d)
        for s in range(0, mind+1):
            lhs = Qseries_def(list(d), s)
            ds = [x - s for x in d]
            rhs = cap(P(s).as_expr() * Qseries_def(ds, 0).as_expr())
            if not eq_upto(lhs, rhs, DEG-6):
                ok = False; print(f"  d={d} s={s}: MISMATCH")
    print(f"  => {'PASS' if ok else 'FAIL'}\n")

    print("Pm corner-change (b):  Pm(m) == P_s * Pm(dropCorner m) for m corner s:")
    # Pm = prod over i<=j of P(m_ij); dropCorner sets (0,N)->0.
    def Pm_of(m, N):
        acc = sp.Poly(sp.Integer(1), q)
        for (i,j), v in m.items():
            acc = cap(acc * P(v))
        return acc
    bok = True
    for d in tests:
        N = len(d)-1
        mind = min(d)
        for s in range(1, mind+1):
            for m in kostant_partitions(list(d), s):
                mdrop = dict(m); mdrop[(0,N)] = 0
                lhs = Pm_of(m, N)
                rhs = cap(P(s).as_expr() * Pm_of(mdrop, N).as_expr())
                if not eq_upto(lhs, rhs, DEG-4):
                    bok = False; print(f"  d={d} s={s} m={m}: MISMATCH")
                break  # one representative per (d,s) suffices to sanity-check the local change
    print(f"  => {'PASS' if bok else 'FAIL'}")
    print()
    print("VERDICT: use S1' (Qseries d s = P_s * Qseries(d-s) 0). It needs ONLY:")
    print("  - the LANDED orbit bijection dropCorner (kostantEquivShift) + codimForm_update_corner,")
    print("  - the Pm corner-change Pm(m)=P_s*Pm(dropCorner m) (one P-factor at (0,N): P_s vs P_0=1),")
    print("  - Finset.sum_bij / mul_sum.   NO (q)_s object, NO (q)_s*P_s=1 lemma needed.")
