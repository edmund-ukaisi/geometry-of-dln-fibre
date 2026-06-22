"""Probe the structure of Thm 5.6 for an inductive / recursive combinatorial proof.

Thm 5.6:  P_d = sum_{m vdash d} q^{c(m)} P_m,  d = (d_0,...,d_N).

Strategy probes:
 (A) Induction on N (peel last vertex d_N): relate Q-side for (d_0..d_N) to (d_0..d_{N-1}).
 (B) The shift lemma 5.7 is ALREADY combinatorial (add-longest bijection); the Pochhammer
     inverse is q-binomial (combinatorial). So Thm 5.5 <= Thm 5.6 combinatorially.
     Here we focus on whether Thm 5.6 itself reduces along N.

We also re-verify the per-r refinement:  sum_s Q^s_d = P_d  (= Thm 5.6).
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from qseries import P_multiset, Q_rd, P_s, pmul, padd, trunc, PREC, pscale_shift
from ctheta import kostant_fast, codimForm

def P_d(d):
    return P_multiset(list(d))

def fivegon(d):
    tot=[0]*PREC
    for r in range(0,min(d)+1):
        tot=padd(tot, Q_rd(d,r))
    return trunc(tot)

# ---- Probe A: does Q^r_d for (d_0..d_N) factor through (d_0..d_{N-1})? ----
# A Kostant partition of d=(d_0..d_N) is a Kostant partition of (d_0..d_{N-1})
# PLUS a choice of how the laces extend to/terminate at vertex N.
# Concretely: intervals NOT touching N are exactly intervals of the truncated quiver.
# Intervals [i,N] (touching N) carry the "new" structure.

# Let's test a candidate recursion on the WHOLE P_d identity.
# P_{d_0..d_N} = P_{d_N} * P_{d_0..d_{N-1}} (LHS factors trivially since P is multiplicative).
# So Thm 5.6 for (d_0..d_N) reads:
#   P_{d_N} * [ sum_{m' vdash (d_0..d_{N-1})} q^{c'(m')} P_{m'} ]   (by induction)
#      ==  sum_{m vdash (d_0..d_N)} q^{c(m)} P_m
# i.e. we must show RHS_N = P_{d_N} * RHS_{N-1}  combinatorially.
# Test this numerically:
def test_recursion(d):
    d=list(d)
    N=len(d)-1
    if N==0:
        return None
    lhs = fivegon(d)                      # RHS_N
    dtrunc = d[:-1]                        # (d_0..d_{N-1})
    rhs = trunc(pmul(P_s(d[-1]), fivegon(dtrunc)))   # P_{d_N} * RHS_{N-1}
    return lhs==rhs, lhs, rhs

print("=== Probe A: RHS_N(d) ?= P_{d_N} * RHS_{N-1}(d_0..d_{N-1})  (peel last vertex) ===")
for d in [(2,2,2),(2,3,2),(1,2,3),(3,2,1),(2,1,3,2),(4,4,4),(1,2,3,4)]:
    res=test_recursion(d)
    if res is None: continue
    ok,lhs,rhs=res
    print(f"  d={d!s:14} peel-last: {'OK' if ok else 'FAIL'}")
    if not ok:
        print("    RHS_N ", lhs[:10]); print("    P*prev", rhs[:10])

print()
print("=== Probe A': peel FIRST vertex d_0 ===")
def test_recursion_first(d):
    d=list(d)
    N=len(d)-1
    if N==0: return None
    lhs=fivegon(d)
    dtrunc=d[1:]
    rhs=trunc(pmul(P_s(d[0]), fivegon(dtrunc)))
    return lhs==rhs, lhs, rhs
for d in [(2,2,2),(2,3,2),(1,2,3),(3,2,1),(2,1,3,2),(4,4,4),(1,2,3,4)]:
    res=test_recursion_first(d)
    if res is None: continue
    ok,lhs,rhs=res
    print(f"  d={d!s:14} peel-first: {'OK' if ok else 'FAIL'}")
