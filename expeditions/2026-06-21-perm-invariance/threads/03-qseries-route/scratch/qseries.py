"""Exact-arithmetic q-series verification for Thm 5.5 (Pseries) and Thm 5.6 (5gon).

Power series in q are represented as Python lists of EXACT Python ints (coefficients),
truncated to degree < PREC. All arithmetic is integer. NO float.

Objects (paper sec:PoincareSection):
  P_s  = 1 / ((1-q)(1-q^2)...(1-q^s))   [inverse q-Pochhammer; P_0 = 1]
       = sum over partitions with at most s parts of q^|mu|
  P_h (multiset h) = prod_i P_{h_i}
  P_m (Kostant partition m) = prod over intervals of P_{m_ij}
  Q^r_d = sum over Kostant partitions m of d with m_{0N}=r of  q^{codim(O_m)} * P_m
  codim(O_m) = sum_{1<=i<=u<=j<=v<=N} m_{(i-1)(j-1)} m_{uv}    (codimForm)

Thm 5.6 (5gon):   P_d = sum_{m vdash d} q^{codim} P_m  =  sum_{s=0}^{min d} Q^s_d
Thm 5.5 (Pseries): Q^r_d = P_r * sum_{s=0}^{min d - r} (-1)^s q^{C(s,2)} P_s * P_{d-r-s}
  where P_{d-r-s} = prod_i P_{d_i - r - s}, and C(s,2) = s(s-1)/2.
"""
from functools import lru_cache
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from ctheta import kostant_fast, codimForm, kostant_partitions

PREC = 40  # truncation degree (keep coefficients for q^0 .. q^{PREC-1})

def trunc(a):
    return a[:PREC] + [0]*(PREC-len(a)) if len(a) < PREC else a[:PREC]

def padd(a, b):
    n = max(len(a), len(b))
    return [ (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n) ]

def pmul(a, b):
    out = [0]*min(PREC, len(a)+len(b)-1) if a and b else []
    for i, ai in enumerate(a):
        if ai == 0: continue
        if i >= PREC: break
        for j, bj in enumerate(b):
            if i+j >= PREC: break
            out[i+j] += ai*bj
    return out

def pscale_shift(a, sign, shift):
    """ sign * q^shift * a """
    out = [0]*PREC
    for i, ai in enumerate(a):
        if i+shift >= PREC: break
        out[i+shift] += sign*ai
    return out

@lru_cache(maxsize=None)
def one_over_1_minus_qk(k):
    """ 1/(1-q^k) = 1 + q^k + q^{2k} + ... truncated """
    out = [0]*PREC
    i = 0
    while i < PREC:
        out[i] = 1
        i += k
    return tuple(out)

@lru_cache(maxsize=None)
def P_s(s):
    """ inverse q-Pochhammer P_s = prod_{k=1}^{s} 1/(1-q^k). P_0 = 1. """
    res = [1] + [0]*(PREC-1)
    for k in range(1, s+1):
        res = pmul(res, list(one_over_1_minus_qk(k)))
    return res

def P_multiset(h):
    """ P_h = prod_i P_{h_i} over a multiset/list h of nonneg ints. """
    res = [1] + [0]*(PREC-1)
    for hi in h:
        res = pmul(res, P_s(hi))
    return res

def P_kostant(m):
    """ P_m = prod over intervals of P_{m_ij}. m is dict {(i,j):mult}. """
    res = [1] + [0]*(PREC-1)
    for (i,j), mult in m.items():
        if mult > 0:
            res = pmul(res, P_s(mult))
    return res

def Q_rd(d, r):
    """ Q^r_d = sum over Kostant partitions m of d with m_{0N}=r of q^{codim} P_m. """
    N = len(d) - 1
    parts = kostant_fast(d, r)
    total = [0]*PREC
    for m in parts:
        c = codimForm(N, m)
        if c >= PREC:
            continue
        pm = P_kostant(m)
        total = padd(total, pscale_shift(pm, 1, c))
    return trunc(total)

def Cbinom2(s):
    return s*(s-1)//2

def Pseries_rhs(d, r):
    """ RHS of Thm 5.5: P_r * sum_{s=0}^{min d - r} (-1)^s q^{C(s,2)} P_s * prod_i P_{d_i-r-s}. """
    mind = min(d)
    acc = [0]*PREC
    for s in range(0, mind - r + 1):
        # prod_i P_{d_i - r - s}; require d_i - r - s >= 0 for all i (since s <= mind-r, ok)
        shifts = [di - r - s for di in d]
        if any(x < 0 for x in shifts):
            continue
        term = pmul(P_s(s), P_multiset(shifts))
        acc = padd(acc, pscale_shift(term, (-1)**s, Cbinom2(s)))
    return trunc(pmul(P_s(r), acc))

def fivegon_rhs(d):
    """ RHS of Thm 5.6: sum_{m vdash d} q^{codim} P_m  (all r summed). """
    total = [0]*PREC
    for r in range(0, min(d)+1):
        total = padd(total, Q_rd(d, r))
    return trunc(total)

# ---------------------------------------------------------------------------
if __name__ == "__main__":
    tests = [
        (2,2,2), (2,3,2), (2,4,2), (3,3,3),
        (1,2,3), (3,2,1), (2,1,3), (1,3,2),     # non-monotone perms
        (1,2,2,3), (3,2,2,1), (2,1,3,2),
        (4,4,4), (2,2,2,2), (1,2,3,4), (4,3,2,1),
        (5,5,6), (6,5,5),
    ]
    print("=== Thm 5.6 (5gon):  P_d  ==  sum_m q^codim P_m  ===")
    for d in tests:
        lhs = P_multiset(d)
        rhs = fivegon_rhs(d)
        ok = lhs == rhs
        print(f"  d={d!s:14}  5gon: {'OK' if ok else 'FAIL'}")
        if not ok:
            print("   LHS", lhs[:12]); print("   RHS", rhs[:12])

    print("\n=== Thm 5.5 (Pseries):  Q^r_d  ==  P_r sum_s (-1)^s q^C(s,2) P_s P_{d-r-s}  ===")
    for d in tests:
        for r in range(0, min(d)+1):
            lhs = Q_rd(d, r)
            rhs = Pseries_rhs(d, r)
            ok = lhs == rhs
            tag = '' if ok else '  <<<< FAIL'
            print(f"  d={d!s:14} r={r}  Pseries: {'OK' if ok else 'FAIL'}{tag}")
            if not ok:
                print("   LHS", lhs[:12]); print("   RHS", rhs[:12])

    print("\n=== sample Q^0 lowest terms (sanity vs Ex 5.4 / Ex 5.10) ===")
    for d in [(2,2,2),(2,3,2),(2,4,2),(3,3,3)]:
        q = Q_rd(d,0)
        lead = next((i for i,c in enumerate(q) if c), None)
        print(f"  Q^0_{d} : theta q^C = {q[lead]} q^{lead}   (head {q[lead:lead+4]})")
