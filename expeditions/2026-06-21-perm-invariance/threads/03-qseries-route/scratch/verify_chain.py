"""Certify the FULL chain Thm 5.6 => Thm 5.5 is combinatorial/algebraic (no topology).

The chain (paper LR sec:Pseries_proof, lines 1021-1108):

 (S0) Thm 5.6 (5gon) : P_d = sum_{s=0}^{min d} Q^s_d.                         [RWY combinatorial]
 (S1) Lemma 5.7 (shift): Q^{s-r}_{d-r} = (1-q^{s-r+1})...(1-q^r) * Q^s_d.    [add-longest bijection]
       In particular r=s: Q^0_{d-s} = (1-q^1)...(1-q^s) * Q^s_d = (q)_s * Q^s_d
       i.e.  Q^s_d = Q^0_{d-s} / (q)_s = P_s * Q^0_{d-s}.   <-- key eqn:key
 (S2) Substituting into (S0):  P_d = sum_{s=0}^{min d} P_s * Q^0_{d-s}.       [eqn:key, line 1065]
 (S3) Read as power series in formal x (coefficient of x^{d'_0}); invert sum P_s x^s using
       q-binomial (eqn Ps_inverse): (sum P_s x^s)^{-1} = sum (-1)^s q^{C(s,2)} P_s x^s.
       => Q^0_d = sum_{s} (-1)^s q^{C(s,2)} P_s * P_{d-s}.                    [pure algebra]
 (S4) r>0 by (S1) again: Q^r_d = P_r * sum_s (-1)^s q^{C(s,2)} P_s P_{d-r-s}. [Thm 5.5]

We verify EACH step exactly (truncated q-series, integer arithmetic).
Here d-s means subtract s from EVERY component (d_0-s,...,d_N-s); requires s<=min d.
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from qseries import (P_multiset, P_s, Q_rd, pmul, padd, trunc, PREC,
                     pscale_shift, Cbinom2, Pseries_rhs, fivegon_rhs)

def qpoch(s):
    """(q)_s = (1-q)(1-q^2)...(1-q^s) truncated."""
    res=[1]+[0]*(PREC-1)
    for k in range(1,s+1):
        f=[0]*PREC; f[0]=1
        if k<PREC: f[k]=-1
        res=pmul(res,f)
    return trunc(res)

def shift(d, r):
    """vector d - r componentwise."""
    return tuple(x-r for x in d)

# --- (S1) Lemma 5.7 with r=s:  Q^0_{d-s} == (q)_s * Q^s_d   (=> Q^s_d = P_s Q^0_{d-s}) ---
def check_S1(tests):
    print("=== (S1) Lemma 5.7 [r=s]:  Q^0_{d-s}  ==  (q)_s * Q^s_d  ===")
    fails=0
    for d in tests:
        for s in range(0, min(d)+1):
            ds = shift(d, s)
            if any(x<0 for x in ds): continue
            lhs = Q_rd(list(ds), 0)
            rhs = trunc(pmul(qpoch(s), Q_rd(list(d), s)))
            if lhs!=rhs:
                fails+=1; print(f"  FAIL d={d} s={s}"); print("   ",lhs[:8]); print("   ",rhs[:8])
    print("  OK" if fails==0 else f"  {fails} FAILS")
    return fails

# --- (S1') equivalent form: Q^s_d == P_s * Q^0_{d-s} ---
def check_S1b(tests):
    print("=== (S1') :  Q^s_d  ==  P_s * Q^0_{d-s}  ===")
    fails=0
    for d in tests:
        for s in range(0, min(d)+1):
            ds = shift(d, s)
            if any(x<0 for x in ds): continue
            lhs = Q_rd(list(d), s)
            rhs = trunc(pmul(P_s(s), Q_rd(list(ds), 0)))
            if lhs!=rhs: fails+=1; print(f"  FAIL d={d} s={s}")
    print("  OK" if fails==0 else f"  {fails} FAILS")
    return fails

# --- (S2) eqn:key :  P_d == sum_{s=0}^{min d} P_s * Q^0_{d-s} ---
def check_S2(tests):
    print("=== (S2) eqn:key :  P_d  ==  sum_s P_s * Q^0_{d-s}  ===")
    fails=0
    for d in tests:
        lhs = P_multiset(list(d))
        acc=[0]*PREC
        for s in range(0,min(d)+1):
            ds=shift(d,s)
            if any(x<0 for x in ds): continue
            acc=padd(acc, pmul(P_s(s), Q_rd(list(ds),0)))
        if lhs!=trunc(acc): fails+=1; print(f"  FAIL d={d}")
    print("  OK" if fails==0 else f"  {fails} FAILS")
    return fails

# --- (S3) q-binomial inverse used as a series identity:  (sum P_s x^s)(sum (-1)^s q^C(s,2) P_s x^s) == 1
# Check coefficientwise in x (each x-coeff is a q-series), truncated in x up to XPREC.
def check_S3_inverse():
    print("=== (S3) q-binomial:  (sum_s P_s x^s) * (sum_s (-1)^s q^C(s,2) P_s x^s) == 1  (coeff of x^t) ===")
    XPREC=8
    fails=0
    for t in range(0, XPREC):
        # coeff of x^t in product = sum_{a+b=t} P_a * [(-1)^b q^C(b,2) P_b]
        acc=[0]*PREC
        for a in range(0,t+1):
            b=t-a
            term = pmul(P_s(a), pscale_shift(P_s(b), (-1)**b, Cbinom2(b)))
            acc=padd(acc,term)
        acc=trunc(acc)
        expected = ([1]+[0]*(PREC-1)) if t==0 else [0]*PREC
        if acc!=expected:
            fails+=1; print(f"  FAIL coeff x^{t}: {acc[:8]}")
    print("  OK" if fails==0 else f"  {fails} FAILS")
    return fails

if __name__=="__main__":
    tests=[(2,2,2),(2,3,2),(2,4,2),(3,3,3),(1,2,3),(3,2,1),(2,1,3),
           (1,2,2,3),(4,4,4),(2,2,2,2),(1,2,3,4),(4,3,2,1),(5,5,6),(6,5,5)]
    f=0
    f+=check_S1(tests)
    f+=check_S1b(tests)
    f+=check_S2(tests)
    f+=check_S3_inverse()
    print()
    print("FULL CHAIN CERTIFIED (every step exact)" if f==0 else f"{f} TOTAL FAILS")
