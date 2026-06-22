"""Thread 06 — Route D pinned: the (1-q^b) recurrence, its EXACT scope, and the base case.

Discovered:  for a <= b,   (1-q^b) RHS(a,b) = RHS(a,b-1)   (zero correction).
Also         (1-q^b) LHS(a,b) = LHS(a,b-1)   where LHS = P_a P_b  (from geomFactor telescope).

So for a <= b both sides obey the SAME (1-q^b) descent in b. Since (1-q^b) is a non-zero-divisor
in Z[[q]], the descent is cancellable: RHS(a,b)=RHS(a,b-1)/(1-q^b) ... but cleaner is to induct.

This script pins:
  (1) the EXACT range where (1-q^b) RHS(a,b) = RHS(a,b-1) holds — is a<=b necessary? what at a>b, a=b?
  (2) where induction-on-b bottoms out: b=a diagonal. Then we need (D) on the DIAGONAL P_a^2.
  (3) the DIAGONAL identity & whether IT telescopes (peel geomFactor(a) on BOTH P_a):
         (1-q^a)^2 RHS(a,a) =? RHS(a-1,a-1) * something  -- discover.
  (4) ALTERNATIVE: symmetric peel — does (1-q^{max}) RHS = RHS(smaller max) hold for ALL a,b
      if we always peel the LARGER index?  i.e. handle a<b by peel-b and b<a by peel-a, a=b by ???
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "03-qseries-route", "scratch"))
from qseries import P_s, pmul, padd, trunc, PREC, pscale_shift

def psub(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)]

def one_minus_qk(k):
    out = [0]*PREC; out[0] = 1
    if k < PREC: out[k] -= 1
    return out

def nz(d):
    return [(i, c) for i, c in enumerate(d) if c != 0]

def durfee_rhs(a, b):
    acc = [0]*PREC
    for r in range(0, min(a, b)+1):
        term = pmul(pmul(P_s(a-r), P_s(r)), P_s(b-r))
        acc = padd(acc, pscale_shift(term, 1, (a-r)*(b-r)))
    return trunc(acc)

def durfee_lhs(a, b):
    return trunc(pmul(P_s(a), P_s(b)))

# (1) EXACT scope of the (1-q^b) RHS descent ------------------------------------------
print("=== (1) where does (1-q^b) RHS(a,b) == RHS(a,b-1)? (all a,b with b>=1, b up to 8) ===")
hold = []; fail = []
for a in range(0, 9):
    for b in range(1, 9):
        lhs = trunc(pmul(one_minus_qk(b), durfee_rhs(a, b)))
        if lhs == durfee_rhs(a, b-1):
            hold.append((a, b))
        else:
            fail.append((a, b))
print("  HOLDS for (a,b):", hold)
print("  FAILS for (a,b):", fail)
print("  --> the descent holds exactly when:", "a <= b" if all(a<=b for a,b in hold) and all(a>b for a,b in fail) else "SEE LIST")

# Boundary: what is RHS(a,b) when a>b (so we never need to peel b below a)?
# By symmetry RHS(a,b)=RHS(b,a). So WLOG a<=b throughout. Confirm RHS symmetric:
print("\n=== RHS symmetric in (a,b)? ===")
sf = 0
for a in range(9):
    for b in range(9):
        if durfee_rhs(a, b) != durfee_rhs(b, a):
            sf += 1
print("  RHS(a,b)==RHS(b,a):", "OK" if sf == 0 else f"{sf} FAIL")

# (3) DIAGONAL base case a=b: peel geomFactor(a) on BOTH P_a.
#  (1-q^a) LHS(a,a) = (1-q^a) P_a^2 = P_a P_{a-1}.  (1-q^a)^2 LHS = P_{a-1}^2 = LHS(a-1,a-1).
#  Does (1-q^a)^2 RHS(a,a) == RHS(a-1,a-1)?  Discover.
print("\n=== (3) DIAGONAL double-peel: (1-q^a)^2 RHS(a,a) - RHS(a-1,a-1) ===")
for a in range(1, 8):
    twice = trunc(pmul(one_minus_qk(a), pmul(one_minus_qk(a), durfee_rhs(a, a))))
    diff = psub(twice, durfee_rhs(a-1, a-1))
    print(f"  a={a}: correction[:8] = {nz(diff)[:8]}")

# (3b) single peel on diagonal: (1-q^a) RHS(a,a) - RHS(a,a-1)  [a > a-1 so descent should FAIL]
print("\n=== (3b) single (1-q^a) RHS(a,a) - RHS(a-1,a) [note a>b'=a-1 after, but RHS(a-1,a)=RHS(a,a-1)] ===")
for a in range(1, 8):
    one = trunc(pmul(one_minus_qk(a), durfee_rhs(a, a)))
    diff = psub(one, durfee_rhs(a-1, a))   # peel b=a: target b-1=a-1, a-arg stays a -> RHS(a,a-1)
    print(f"  a={a}: (1-q^a)RHS(a,a)-RHS(a,a-1) correction[:8] = {nz(diff)[:8]}")

# So the FULL induction: on b descending to a (peel b, a<=b), THEN on the diagonal peel one factor
# to RHS(a,a-1) [which has a> b'=a-1, use symmetry = RHS(a-1,a), a-1<=a so it's in-range].
# Net: a SINGLE recurrence  (1-q^{max(a,b)}) RHS(a,b) = RHS with max reduced by 1, for a != b OR a=b.
# Test the UNIFIED claim:  for all (a,b) not both zero, with M=max(a,b),
#     (1-q^M) RHS(a,b) = RHS(a',b') where (a',b') = (a,b) with the max coordinate reduced by 1.
print("\n=== (4) UNIFIED peel-the-max recurrence: (1-q^{max}) RHS(a,b) = RHS(max reduced by 1) ===")
uf = 0; uhold = 0
for a in range(0, 9):
    for b in range(0, 9):
        if a == 0 and b == 0:
            continue
        M = max(a, b)
        if a >= b:
            ap, bp = a-1, b
        else:
            ap, bp = a, b-1
        lhs = trunc(pmul(one_minus_qk(M), durfee_rhs(a, b)))
        if lhs == durfee_rhs(ap, bp):
            uhold += 1
        else:
            uf += 1
            if uf <= 8:
                print(f"   FAIL a={a} b={b} M={M} -> ({ap},{bp})")
print(f"  unified peel-the-max: {uhold} hold, {uf} fail")
